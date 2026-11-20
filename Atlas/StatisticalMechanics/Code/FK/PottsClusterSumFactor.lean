/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Percolation.BurtonKeane
import Code.IsingFK.Coloring










open MeasureTheory Set

namespace StatMech.FK

open Lattice Percolation


def pottsLabelShift {d q : Nat} (g : Multiplicative (Site d))
    (label : Site d -> Fin q) : Site d -> Fin q :=
  fun x => label (g⁻¹ • x)



noncomputable def pottsClusterSumSpin {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) (x : Site d) : Fin q := by
  classical
  exact if hfinite : (cluster d omega x).Finite then
      ∑ y ∈ hfinite.toFinset, label y
    else boundaryColor


theorem pottsClusterSumSpin_eq_of_connected {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) {x y : Site d}
    (hxy : Connected d omega x y) :
    pottsClusterSumSpin boundaryColor omega label x =
      pottsClusterSumSpin boundaryColor omega label y := by
  classical
  unfold pottsClusterSumSpin
  rw [cluster_eq_of_connected hxy]


theorem pottsClusterSumSpin_constOnOpen {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) :
    ConstOnOpen (hypercubicLattice d) omega
      (pottsClusterSumSpin boundaryColor omega label) := by
  intro x y hxy
  exact pottsClusterSumSpin_eq_of_connected boundaryColor omega label
    hxy.reachable


theorem pottsClusterSumSpin_of_infinite {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) (x : Site d)
    (hinfinite : (cluster d omega x).Infinite) :
    pottsClusterSumSpin boundaryColor omega label x = boundaryColor := by
  classical
  rw [pottsClusterSumSpin, dif_neg hinfinite]


theorem pottsClusterSumSpin_of_finite {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (label : Site d -> Fin q) (x : Site d)
    (hfinite : (cluster d omega x).Finite) :
    pottsClusterSumSpin boundaryColor omega label x =
      ∑ y ∈ hfinite.toFinset, label y := by
  classical
  rw [pottsClusterSumSpin, dif_pos hfinite]



theorem pottsClusterSumSpin_shift {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (label : Site d -> Fin q)
    (x : Site d) :
    pottsClusterSumSpin boundaryColor (ConfigSpace.shift g omega)
        (pottsLabelShift g label) (g • x) =
      pottsClusterSumSpin boundaryColor omega label x := by
  classical
  rw [pottsClusterSumSpin, pottsClusterSumSpin, cluster_shift]
  by_cases hfinite : (cluster d omega x).Finite
  · have himage : ((fun y => g • y) '' cluster d omega x).Finite :=
      hfinite.image _
    rw [dif_pos himage, dif_pos hfinite]
    rw [Set.Finite.toFinset_image (fun y => g • y) hfinite himage]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro y hy
      simp [pottsLabelShift]
    · intro a ha b hb hab
      exact smul_left_cancel g hab
  · have himage : ¬((fun y => g • y) '' cluster d omega x).Finite := by
      intro h
      apply hfinite
      have hpre : cluster d omega x =
          (fun y => g⁻¹ • y) '' ((fun y => g • y) '' cluster d omega x) := by
        ext y
        simp
      rw [hpre]
      exact h.image _
    rw [dif_neg himage, dif_neg hfinite]




def pottsLabelTwist {ι : Type*} [DecidableEq ι] {q : Nat} [NeZero q]
    (root : ι) (increment : Fin q) (label : ι -> Fin q) : ι -> Fin q :=
  Function.update label root (label root + increment)



theorem sum_pottsLabelTwist {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : Nat} [NeZero q] (root : ι) (increment : Fin q)
    (label : ι -> Fin q) :
    ∑ i, pottsLabelTwist root increment label i =
      (∑ i, label i) + increment := by
  rw [pottsLabelTwist, Finset.sum_update_of_mem (Finset.mem_univ root)]
  simp
  abel


noncomputable def pottsLabelTwistEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : Nat} [NeZero q] (root : ι) (increment : Fin q) :
    (ι -> Fin q) ≃ (ι -> Fin q) where
  toFun := pottsLabelTwist root increment
  invFun := pottsLabelTwist root (-increment)
  left_inv label := by
    funext i
    by_cases hi : i = root
    · subst i
      simp [pottsLabelTwist]
    · simp [pottsLabelTwist, hi]
  right_inv label := by
    funext i
    by_cases hi : i = root
    · subst i
      simp [pottsLabelTwist]
    · simp [pottsLabelTwist, hi]




noncomputable def pottsClusterSumFiberEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a b : Fin q) :
    {label : ι -> Fin q // ∑ i, label i = a} ≃
      {label : ι -> Fin q // ∑ i, label i = b} := by
  let root : ι := Classical.choice inferInstance
  let twist := pottsLabelTwistEquiv root (b - a)
  refine
    { toFun := fun label => ⟨twist label, ?_⟩
      invFun := fun label => ⟨twist.symm label, ?_⟩
      left_inv := fun label => Subtype.ext (twist.left_inv label)
      right_inv := fun label => Subtype.ext (twist.right_inv label) }
  · change ∑ i, pottsLabelTwist root (b - a) label.1 i = b
    rw [sum_pottsLabelTwist, label.2]
    abel
  · change ∑ i, pottsLabelTwist root (-(b - a)) label.1 i = a
    rw [sum_pottsLabelTwist, label.2]
    abel


theorem card_pottsClusterSumFiber_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a b : Fin q) :
    Fintype.card {label : ι -> Fin q // ∑ i, label i = a} =
      Fintype.card {label : ι -> Fin q // ∑ i, label i = b} :=
  Fintype.card_congr (pottsClusterSumFiberEquiv a b)



theorem card_pottsClusterSumFiber_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a : Fin q) :
    q * Fintype.card {label : ι -> Fin q // ∑ i, label i = a} =
      Fintype.card (ι -> Fin q) := by
  let sumMap : (ι -> Fin q) -> Fin q := fun label => ∑ i, label i
  have htotal := Fintype.card_congr (Equiv.sigmaFiberEquiv sumMap)
  rw [Fintype.card_sigma] at htotal
  have hfiber : ∀ b : Fin q,
      Fintype.card {label : ι -> Fin q // sumMap label = b} =
        Fintype.card {label : ι -> Fin q // sumMap label = a} := by
    intro b
    exact card_pottsClusterSumFiber_eq b a
  simp_rw [hfiber] at htotal
  simpa [Fintype.card_fin, Finset.sum_const] using htotal



theorem pottsUniformPi_eq_uniform
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : Nat} [NeZero q] :
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) =
      (PMF.uniformOfFintype (ι -> Fin q)).toMeasure := by
  apply Measure.ext_of_singleton
  intro label
  rw [Measure.pi_singleton]
  have hinvpow : ∀ n : Nat,
      (q : ENNReal)⁻¹ ^ n = ((q : ENNReal) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ, ih,
          ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top q))
            (Or.inr (by exact_mod_cast (Nat.pos_of_neZero q).ne'))]
  simp [Fintype.card_fin, hinvpow]



theorem pottsUniformPi_sum_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] (a : Fin q) :
    Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure)
        {label | ∑ i, label i = a} = (q : ENNReal)⁻¹ := by
  rw [pottsUniformPi_eq_uniform]
  rw [PMF.toMeasure_uniformOfFintype_apply _
    (Set.toFinite {label : ι -> Fin q | ∑ i, label i = a} |>.measurableSet)]
  rw [Fintype.card_subtype]
  have hcard := card_pottsClusterSumFiber_mul (ι := ι) a
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype] at hcard
  rw [Fintype.card_fun, Fintype.card_fin, ENNReal.div_eq_inv_mul]
  have hcast : (q : ENNReal) *
      (↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) : ENNReal) =
      (↑(q ^ Fintype.card ι) : ENNReal) := by
    exact_mod_cast hcard
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  let root : ι := Classical.choice inferInstance
  let witness : ι -> Fin q := pottsLabelTwist root a (fun _ => 0)
  have hwitness : ∑ i, witness i = a := by
    simp [witness, sum_pottsLabelTwist]
  letI : Nonempty {label : ι -> Fin q // ∑ i, label i = a} :=
    ⟨⟨witness, hwitness⟩⟩
  calc
    (↑(q ^ Fintype.card ι) : ENNReal)⁻¹ *
        ↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) =
      ((q : ENNReal) *
        ↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card))⁻¹ *
        ↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) := by
      rw [hcast]
    _ = (q : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv
        (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl hqtop), mul_assoc]
      have hfiber0 :
          (↑((Finset.univ.filter fun label : ι -> Fin q => ∑ i, label i = a).card) :
            ENNReal) ≠ 0 := by
        rw [← Fintype.card_subtype]
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card
          {label : ι -> Fin q // ∑ i, label i = a} ≠ 0)
      rw [ENNReal.inv_mul_cancel hfiber0 (ENNReal.natCast_ne_top _)]
      simp



theorem pottsUniformPi_sum_map
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {q : Nat} [NeZero q] :
    Measure.map (fun label : ι -> Fin q => ∑ i, label i)
        (Measure.pi fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) =
      (PMF.uniformOfFintype (Fin q)).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply_of_aemeasurable Measurable.of_discrete.aemeasurable
    (Set.toFinite ({a} : Set (Fin q)) |>.measurableSet)]
  change Measure.pi (fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure)
      {label | ∑ i, label i = a} = _
  rw [pottsUniformPi_sum_apply]
  simp


def pottsBlockLabels {κ ι q : Type*} (F : κ -> Finset ι)
    (label : ι -> q) : ∀ k, F k -> q :=
  fun _ x => label x


def pottsBlockSums {κ ι : Type*} {q : Nat} [NeZero q]
    (F : κ -> Finset ι) (label : ι -> Fin q) : κ -> Fin q :=
  fun k => ∑ x : F k, label x



theorem pottsIID_blockLabels_law
    {κ ι : Type*} [DecidableEq ι] {q : Nat} [NeZero q]
    (F : κ -> Finset ι)
    (hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l)) :
    Measure.map (pottsBlockLabels F)
        (Measure.infinitePi fun _ : ι =>
          (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.infinitePi fun k : κ =>
        Measure.infinitePi fun _ : F k =>
          (PMF.uniformOfFintype (Fin q)).toMeasure := by
  let embed : ((k : κ) × F k) -> ι := fun p => p.2
  have hembed : Function.Injective embed := by
    rintro ⟨k, x⟩ ⟨l, y⟩ hxy
    change (x : ι) = (y : ι) at hxy
    have hkl : k = l := by
      by_contra hne
      have hx : (x : ι) ∈ F k := x.2
      have hy : (x : ι) ∈ F l := by rw [hxy]; exact y.2
      exact Finset.disjoint_left.mp (hdisjoint k l hne) hx hy
    subst l
    simp_all
  have hflat : Measure.map (fun label : ι -> Fin q =>
        fun p : ((k : κ) × F k) => label (embed p))
      (Measure.infinitePi fun _ : ι =>
        (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.infinitePi fun _ : ((k : κ) × F k) =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
    simpa using (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ι => (PMF.uniformOfFintype (Fin q)).toMeasure) hembed)
  have hfactor : pottsBlockLabels F =
      (MeasurableEquiv.piCurry (fun _ : κ => fun _ : F _ => Fin q)) ∘
        (fun label : ι -> Fin q =>
          fun p : ((k : κ) × F k) => label (embed p)) := by
    funext label k x
    rfl
  rw [hfactor, ← Measure.map_map
    (MeasurableEquiv.piCurry (fun _ : κ => fun _ : F _ => Fin q)).measurable
    (measurable_pi_lambda _ fun p => measurable_pi_apply (embed p)), hflat]
  rw [← Measure.infinitePi_map_piCurry_symm
    (fun _ : κ => fun _ : F _ =>
      (PMF.uniformOfFintype (Fin q)).toMeasure)]
  rw [Measure.map_map]
  · simp
  · exact (MeasurableEquiv.piCurry
      (fun _ : κ => fun _ : F _ => Fin q)).measurable
  · exact (MeasurableEquiv.piCurry
      (fun _ : κ => fun _ : F _ => Fin q)).symm.measurable



theorem pottsIID_blockSums_law
    {κ ι : Type*} [DecidableEq ι] {q : Nat} [NeZero q]
    (F : κ -> Finset ι) (hF : ∀ k, (F k).Nonempty)
    (hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l)) :
    Measure.map (pottsBlockSums F)
        (Measure.infinitePi fun _ : ι =>
          (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.infinitePi fun _ : κ =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
  have hfactor : pottsBlockSums F =
      (fun block : ∀ k, F k -> Fin q => fun k => ∑ x, block k x) ∘
        pottsBlockLabels F := by
    rfl
  rw [hfactor]
  calc
    Measure.map
        ((fun block : ∀ k, F k -> Fin q => fun k => ∑ x, block k x) ∘
          pottsBlockLabels F)
        (Measure.infinitePi fun _ : ι =>
          (PMF.uniformOfFintype (Fin q)).toMeasure) =
      Measure.map (fun block : ∀ k, F k -> Fin q =>
          fun k => ∑ x, block k x)
        (Measure.map (pottsBlockLabels F)
          (Measure.infinitePi fun _ : ι =>
            (PMF.uniformOfFintype (Fin q)).toMeasure)) := by
      have houter : Measurable (fun block : ∀ k, F k -> Fin q =>
          fun k => ∑ x, block k x) :=
        measurable_pi_lambda _ fun k =>
          Finset.univ.measurable_fun_sum fun x _ =>
            (measurable_pi_apply x).comp (measurable_pi_apply k)
      have hinner : Measurable (pottsBlockLabels F :
          (ι -> Fin q) -> ∀ k, F k -> Fin q) := by
        unfold pottsBlockLabels
        exact measurable_pi_lambda _ fun _ =>
          measurable_pi_lambda _ fun x => measurable_pi_apply (x : ι)
      exact (Measure.map_map houter hinner).symm
    _ = Measure.map (fun block : ∀ k, F k -> Fin q =>
          fun k => ∑ x, block k x)
        (Measure.infinitePi fun k : κ =>
          Measure.infinitePi fun _ : F k =>
            (PMF.uniformOfFintype (Fin q)).toMeasure) := by
      rw [pottsIID_blockLabels_law F hdisjoint]
    _ = Measure.infinitePi fun _ : κ =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
      rw [Measure.infinitePi_map_pi
        (fun k : κ => Measure.infinitePi fun _ : F k =>
          (PMF.uniformOfFintype (Fin q)).toMeasure)
        (fun k => Finset.univ.measurable_fun_sum fun x _ => measurable_pi_apply x)]
      congrm Measure.infinitePi fun k => ?_
      letI : Nonempty (F k) := by
        obtain ⟨x, hx⟩ := hF k
        exact ⟨⟨x, hx⟩⟩
      rw [Measure.infinitePi_eq_pi]
      exact pottsUniformPi_sum_map





noncomputable def pottsClusterSumJointFactor {d q : Nat} [NeZero q]
    (boundaryColor : Fin q)
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :
    (Site d -> Fin q) × ConfigSpace (Sym2 (Site d)) :=
  (pottsClusterSumSpin boundaryColor input.1 input.2, input.1)


noncomputable def pottsClusterFactorInputShift {d q : Nat}
    (g : Multiplicative (Site d))
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :
    ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) :=
  (ConfigSpace.shift g input.1, pottsLabelShift g input.2)


noncomputable def pottsJointShift {d q : Nat} (g : Multiplicative (Site d))
    (joint : (Site d -> Fin q) × ConfigSpace (Sym2 (Site d))) :
    (Site d -> Fin q) × ConfigSpace (Sym2 (Site d)) :=
  (pottsLabelShift g joint.1, ConfigSpace.shift g joint.2)



theorem pottsClusterSumJointFactor_shift {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (g : Multiplicative (Site d))
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :
    pottsClusterSumJointFactor boundaryColor
        (pottsClusterFactorInputShift g input) =
      pottsJointShift g (pottsClusterSumJointFactor boundaryColor input) := by
  apply Prod.ext
  · funext x
    have h := pottsClusterSumSpin_shift boundaryColor g input.1 input.2
      (g⁻¹ • x)
    simpa [pottsClusterSumJointFactor, pottsClusterFactorInputShift,
      pottsJointShift, pottsLabelShift] using h
  · rfl





def pottsClusterEqEvent (d : Nat) (x : Site d) (F : Finset (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | cluster d omega x = (F : Set (Site d))}

theorem measurableSet_pottsClusterEqEvent
    (d : Nat) (x : Site d) (F : Finset (Site d)) :
    MeasurableSet (pottsClusterEqEvent d x F) := by
  have heq : pottsClusterEqEvent d x F =
      ⋂ y : Site d, if y ∈ F then
        {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y}
      else
        {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y}ᶜ := by
    ext omega
    simp only [pottsClusterEqEvent, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h y
      by_cases hy : y ∈ F
      · rw [if_pos hy]
        change Connected d omega x y
        rw [← mem_cluster, h]
        exact hy
      · rw [if_neg hy]
        change ¬Connected d omega x y
        intro hconn
        apply hy
        have hmem : y ∈ cluster d omega x := hconn
        have hmemF : y ∈ (F : Set (Site d)) := by
          rw [← h]
          exact hmem
        simpa using hmemF
    · intro h
      ext y
      specialize h y
      by_cases hy : y ∈ F
      · have hconn : Connected d omega x y := by
          simpa [hy] using h
        exact iff_of_true hconn hy
      · have hnconn : ¬Connected d omega x y := by
          simpa [hy] using h
        exact iff_of_false hnconn hy
  rw [heq]
  apply MeasurableSet.iInter
  intro y
  by_cases hy : y ∈ F
  · rw [if_pos hy]
    exact measurableSet_connected x y
  · rw [if_neg hy]
    exact (measurableSet_connected x y).compl


def pottsLabelSumEvent {d q : Nat} [NeZero q]
    (F : Finset (Site d)) (a : Fin q) :
    Set (Site d -> Fin q) :=
  cylinder (α := fun _ : Site d => Fin q) F
    {label | ∑ x, label x = a}

theorem measurableSet_pottsLabelSumEvent {d q : Nat} [NeZero q]
    (F : Finset (Site d)) (a : Fin q) :
    MeasurableSet (pottsLabelSumEvent F a) := by
  unfold pottsLabelSumEvent cylinder
  apply MeasurableSet.preimage
  · exact Set.toFinite {label : F -> Fin q | ∑ x, label x = a} |>.measurableSet
  · exact measurable_pi_lambda _ fun x => measurable_pi_apply x.1



def pottsClusterSumFiberEvent {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (x : Site d) (a : Fin q) :
    Set (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
  (if a = boundaryColor then
      Prod.fst ⁻¹'
        {omega : ConfigSpace (Sym2 (Site d)) |
          (cluster d omega x).Infinite}
    else ∅) ∪
    ⋃ F : Finset (Site d),
      Prod.fst ⁻¹' pottsClusterEqEvent d x F ∩
        Prod.snd ⁻¹' pottsLabelSumEvent F a

theorem measurableSet_pottsClusterSumFiberEvent
    {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (x : Site d) (a : Fin q) :
    MeasurableSet (pottsClusterSumFiberEvent boundaryColor x a) := by
  unfold pottsClusterSumFiberEvent
  apply MeasurableSet.union
  · by_cases ha : a = boundaryColor
    · rw [if_pos ha]
      exact (measurableSet_clusterInfinite x).preimage measurable_fst
    · rw [if_neg ha]
      exact MeasurableSet.empty
  · apply MeasurableSet.iUnion
    intro F
    exact ((measurableSet_pottsClusterEqEvent d x F).preimage measurable_fst).inter
      ((measurableSet_pottsLabelSumEvent F a).preimage measurable_snd)


theorem pottsClusterSumFiberEvent_eq
    {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (x : Site d) (a : Fin q) :
    pottsClusterSumFiberEvent boundaryColor x a =
      {input | pottsClusterSumSpin boundaryColor input.1 input.2 x = a} := by
  classical
  ext input
  constructor
  · intro h
    change pottsClusterSumSpin boundaryColor input.1 input.2 x = a
    rcases h with hinfinite | hfinite
    · by_cases ha : a = boundaryColor
      · have hinf : (cluster d input.1 x).Infinite := by
          simpa [pottsClusterSumFiberEvent, ha] using hinfinite
        simpa [ha] using
          pottsClusterSumSpin_of_infinite boundaryColor input.1 input.2 x hinf
      · simpa [pottsClusterSumFiberEvent, ha] using hinfinite
    · rw [Set.mem_iUnion] at hfinite
      obtain ⟨F, hcluster, hlabel⟩ := hfinite
      have hclusterEq : cluster d input.1 x = (F : Set (Site d)) :=
        hcluster
      have hfin : (cluster d input.1 x).Finite := by
        rw [hclusterEq]
        exact F.finite_toSet
      have hfinset : hfin.toFinset = F := by
        ext y
        simp [hclusterEq]
      have hsum : ∑ y : F, input.2 y = a := by
        simpa [pottsLabelSumEvent] using hlabel
      rw [pottsClusterSumSpin_of_finite boundaryColor input.1 input.2 x hfin,
        hfinset]
      exact (Finset.sum_subtype F (by simp) input.2).trans hsum
  · intro hspin
    change pottsClusterSumSpin boundaryColor input.1 input.2 x = a at hspin
    by_cases hfin : (cluster d input.1 x).Finite
    · right
      rw [Set.mem_iUnion]
      refine ⟨hfin.toFinset, ?_, ?_⟩
      · change cluster d input.1 x = (hfin.toFinset : Set (Site d))
        exact hfin.coe_toFinset.symm
      · have hsum : ∑ y ∈ hfin.toFinset, input.2 y = a := by
          rw [← pottsClusterSumSpin_of_finite
            boundaryColor input.1 input.2 x hfin]
          exact hspin
        change input.2 ∈ pottsLabelSumEvent hfin.toFinset a
        simp only [pottsLabelSumEvent, mem_cylinder, Set.mem_setOf_eq]
        have hsub : (∑ y ∈ hfin.toFinset, input.2 y) =
            ∑ y : hfin.toFinset, input.2 y :=
          Finset.sum_subtype hfin.toFinset (fun _ => Iff.rfl) input.2
        change (∑ y : hfin.toFinset, input.2 y) = a
        rw [← hsub]
        exact hsum
    · left
      have ha : a = boundaryColor := by
        have hpin := pottsClusterSumSpin_of_infinite
          boundaryColor input.1 input.2 x hfin
        exact hspin.symm.trans hpin
      have hinf : (cluster d input.1 x).Infinite := hfin
      simpa [pottsClusterSumFiberEvent, ha] using hinf


theorem measurable_pottsClusterSumSpin_apply
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (x : Site d) :
    Measurable (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor input.1 input.2 x) := by
  rw [measurable_iff_comap_le]
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have heq : (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor input.1 input.2 x) ⁻¹' t =
      ⋃ a ∈ t, pottsClusterSumFiberEvent boundaryColor x a := by
    ext input
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨pottsClusterSumSpin boundaryColor input.1 input.2 x, ⟨h, ?_⟩⟩
      rw [pottsClusterSumFiberEvent_eq]
      rfl
    · intro h
      obtain ⟨a, ha, hfiber⟩ := h
      rw [pottsClusterSumFiberEvent_eq] at hfiber
      rwa [hfiber]
  rw [heq]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ =>
    measurableSet_pottsClusterSumFiberEvent boundaryColor x a



theorem measurable_pottsClusterSumSpin
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) :
    Measurable (fun input :
      ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) =>
        pottsClusterSumSpin boundaryColor input.1 input.2) :=
  measurable_pi_lambda _ fun x =>
    measurable_pottsClusterSumSpin_apply boundaryColor x


theorem measurable_pottsClusterSumJointFactor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) :
    Measurable (pottsClusterSumJointFactor boundaryColor :
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) ->
        ((Site d -> Fin q) × ConfigSpace (Sym2 (Site d)))) :=
  (measurable_pottsClusterSumSpin boundaryColor).prodMk measurable_fst




noncomputable def pottsIIDLabelMeasure (d q : Nat) [NeZero q] :
    Measure (Site d -> Fin q) :=
  Measure.infinitePi fun _ : Site d =>
    (PMF.uniformOfFintype (Fin q)).toMeasure


theorem pottsIIDLabelMeasure_pottsLabelSumEvent
    {d q : Nat} [NeZero q] (F : Finset (Site d)) (hF : F.Nonempty)
    (a : Fin q) :
    pottsIIDLabelMeasure d q (pottsLabelSumEvent F a) =
      (q : ENNReal)⁻¹ := by
  letI : Nonempty F := by
    obtain ⟨x, hx⟩ := hF
    exact ⟨⟨x, hx⟩⟩
  unfold pottsIIDLabelMeasure pottsLabelSumEvent
  calc
    (Measure.infinitePi fun _ : Site d =>
        (PMF.uniformOfFintype (Fin q)).toMeasure)
        (cylinder F {label | ∑ x, label x = a}) =
      Measure.pi (fun _ : F =>
        (PMF.uniformOfFintype (Fin q)).toMeasure)
        {label | ∑ x, label x = a} :=
      Measure.infinitePi_cylinder
        (fun _ : Site d => (PMF.uniformOfFintype (Fin q)).toMeasure)
        (Set.toFinite {label : F -> Fin q | ∑ x, label x = a} |>.measurableSet)
    _ = (q : ENNReal)⁻¹ := pottsUniformPi_sum_apply a



theorem pottsClusterSumSpin_representatives_law
    {d q : Nat} [NeZero q] {κ : Type*}
    (boundaryColor : Fin q) (omega : ConfigSpace (Sym2 (Site d)))
    (r : κ -> Site d)
    (hfinite : ∀ k, (cluster d omega (r k)).Finite)
    (hdistinct : ∀ k l, k ≠ l -> ¬Connected d omega (r k) (r l)) :
    Measure.map (fun label k =>
        pottsClusterSumSpin boundaryColor omega label (r k))
        (pottsIIDLabelMeasure d q) =
      Measure.infinitePi fun _ : κ =>
        (PMF.uniformOfFintype (Fin q)).toMeasure := by
  let F : κ -> Finset (Site d) := fun k => (hfinite k).toFinset
  have hF : ∀ k, (F k).Nonempty := by
    intro k
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hself : r k ∈ F k := by
      change r k ∈ (hfinite k).toFinset
      simpa only [Set.Finite.mem_toFinset] using self_mem_cluster omega (r k)
    simpa [hempty] using hself
  have hdisjoint : ∀ k l, k ≠ l -> Disjoint (F k) (F l) := by
    intro k l hne
    apply Finset.disjoint_left.mpr
    intro z hzk hzl
    have hzk' : z ∈ cluster d omega (r k) := by
      simpa [F] using hzk
    have hzl' : z ∈ cluster d omega (r l) := by
      simpa [F] using hzl
    apply hdistinct k l hne
    exact (mem_cluster.mp hzk').trans (mem_cluster.mp hzl').symm
  have hfactor : (fun label k =>
        pottsClusterSumSpin boundaryColor omega label (r k)) =
      pottsBlockSums F := by
    funext label k
    rw [pottsClusterSumSpin_of_finite boundaryColor omega label (r k) (hfinite k)]
    exact Finset.sum_subtype (F k) (fun _ => Iff.rfl) label
  rw [hfactor]
  exact pottsIID_blockSums_law F hF hdisjoint

instance pottsIIDLabelMeasure_isProbabilityMeasure
    (d q : Nat) [NeZero q] :
    IsProbabilityMeasure (pottsIIDLabelMeasure d q) := by
  unfold pottsIIDLabelMeasure
  infer_instance




noncomputable def pottsClusterSumJointMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))) :
    Measure ((Site d -> Fin q) × ConfigSpace (Sym2 (Site d))) :=
  Measure.map (pottsClusterSumJointFactor boundaryColor)
    (edgeMeasure.prod (pottsIIDLabelMeasure d q))



theorem pottsClusterSumJointMeasure_isProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] :
    IsProbabilityMeasure
      (pottsClusterSumJointMeasure boundaryColor edgeMeasure) := by
  unfold pottsClusterSumJointMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_pottsClusterSumJointFactor boundaryColor).aemeasurable



theorem pottsClusterSumJointMeasure_map_snd
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure edgeMeasure] :
    Measure.map Prod.snd
        (pottsClusterSumJointMeasure boundaryColor edgeMeasure) =
      edgeMeasure := by
  rw [pottsClusterSumJointMeasure,
    Measure.map_map measurable_snd
      (measurable_pottsClusterSumJointFactor boundaryColor)]
  change Measure.map Prod.fst
      (edgeMeasure.prod (pottsIIDLabelMeasure d q)) = edgeMeasure
  exact measurePreserving_fst.map_eq

end StatMech.FK
