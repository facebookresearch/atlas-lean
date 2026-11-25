/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Power-equation type and almost simple groups

The theorem `conjecture_refuted` proves that power-equation type does not characterize almost
simple groups. It uses explicit degree-23 permutation groups obtained from the pair and heptad
stabilizers in Li and Shi's counterexample. Stabilizer-chain certificates verify the groups'
structure and the equality of their element-order counts.
-/

namespace MathlibExt.GroupTheory.Kourovka21Problem134bWanted

@[expose] public section

universe u

/-- **Same power-equation type.** Two groups $G$ and $H$ have the same power-equation type when,
for every positive integer $n$, the equation $x^n = 1$ has the same number of solutions in $G$ as
in $H$. An infinite set of solutions is counted as $0$, so the notion is meant for finite
groups. -/
def SamePowerEquationType (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ n : ℕ, 0 < n →
    Nat.card {x : G // x ^ n = 1} = Nat.card {x : H // x ^ n = 1}

/-- **Almost simple group.** A group $G$ is almost simple when there is a nonabelian finite simple
group $S$ such that $G$ is isomorphic to a subgroup $A$ of the automorphism group
$\mathrm{Aut}(S)$ that contains the inner automorphism group $\mathrm{Inn}(S)$. -/
def IsAlmostSimple (G : Type u) [Group G] : Prop :=
  ∃ (S : Type u) (groupStructure : Group S) (finiteS : Finite S)
      (simpleS : IsSimpleGroup S),
    letI := groupStructure
    letI := finiteS
    letI := simpleS
    ¬IsMulCommutative S ∧
      ∃ A : Subgroup (MulAut S),
        MonoidHom.range (MulAut.conj : S →* MulAut S) ≤ A ∧
          Nonempty (G ≃* A)

/-- **Characterization of almost simple groups by power-equation type (Kourovka 21.134(b)).**
The conjecture that for all finite groups $G$ and $H$, if $G$ is almost simple and $G$ and $H$
have the same power-equation type, then $G$ is isomorphic to $H$. -/
def conjecture : Prop :=
  ∀ (G H : Type*) [Group G] [Finite G] [Group H] [Finite H],
    IsAlmostSimple G → SamePowerEquationType G H → Nonempty (G ≃* H)

end

open Equiv

private abbrev P := Equiv.Perm (Fin 23)

/- The permutation data list the images in base 32, with the image of 0 in the
least significant digit. Each entry supplies an inverse whose two compositions
with the forward permutation are checked on all 23 points. -/
private def unpack (code : Nat) (i : Fin 23) : Fin 23 :=
  ⟨((code >>> (5 * i.val)) &&& 31) % 23, Nat.mod_lt _ (by decide)⟩

private def packed (code inverse : Nat)
    (h : (∀ i, unpack inverse (unpack code i) = i) ∧
      (∀ i, unpack code (unpack inverse i) = i)) : P :=
  ⟨unpack code, unpack inverse, h.1, h.2⟩

/- A stabilizer-chain level records a base point, the extra generators at this
level, and left coset representatives paired with words in the generators.
The levels are listed from the whole group down to the trivial group. -/
private structure Level where
  point : Fin 23
  lifts : List P
  reps : List (P × List Nat)

private def pair0 : Level where
  point := 5
  lifts := [
    packed 21149014882718007510795999145723936
      17224023597723684935085480707459104 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 21149014882718007510795999145723936
      17224023597723684935085480707459104 (by decide +kernel), [0]),
    (packed 17224023597723684935085480707459104
      21149014882718007510795999145723936 (by decide +kernel), [0, 0])]

private def pair1 : Level where
  point := 4
  lifts := [
    packed 9746232050451908501780066813970464
      9746232050451908501780066813970464 (by decide +kernel),
    packed 8339264913346975636621282356856864
      8339264913346975636621282356856864 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 9746232050451908501780066813970464
      9746232050451908501780066813970464 (by decide +kernel), [0]),
    (packed 8339264913346975636621282356856864
      8339264913346975636621282356856864 (by decide +kernel), [1]),
    (packed 16445493887627351993936736990365728
      20346086079600431876274273725286432 (by decide +kernel), [1, 2, 0]),
    (packed 26133266016585805119667280265971744
      9480099582244954774698510831945760 (by decide +kernel), [1, 0, 2, 1]),
    (packed 20371673964484842669988457203468320
      27888680184962752334443789918767136 (by decide +kernel), [2, 1]),
    (packed 23655125450927563503526748921890848
      13238855680449285518178617634424864 (by decide +kernel), [0, 2, 1]),
    (packed 24034283315618573087829625399248928
      25121772452457763312800911875737632 (by decide +kernel), [2, 2, 1]),
    (packed 5646444389193062444091493351262240
      17296427879406494959971276756715552 (by decide +kernel), [2, 2, 1, 0]),
    (packed 13535599455901124075072634242566176
      25491604893941797862406101447837728 (by decide +kernel), [2, 0]),
    (packed 6026793697417781017620123956119584
      21526475516956751246909948494448672 (by decide +kernel), [2, 1, 0]),
    (packed 15070126411289325635615674521978912
      11982670887287376714964203415373856 (by decide +kernel), [0, 2, 0]),
    (packed 8199971786665308201317631209343008
      12355958966072381278280338871781408 (by decide +kernel), [2, 0, 2, 1]),
    (packed 12355958966072381278280338871781408
      8199971786665308201317631209343008 (by decide +kernel), [1, 0, 2, 0]),
    (packed 8132473978768993794263732077037600
      14454276356560267748269578306816032 (by decide +kernel), [0, 2, 1, 0]),
    (packed 5982885655848120470344932700293152
      5982885655848120470344932700293152 (by decide +kernel), [1, 0])]

private def pair2 : Level where
  point := 3
  lifts := [
    packed 22321094333208014997106376689453088
      18439536166448984518321637084891168 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 22321094333208014997106376689453088
      18439536166448984518321637084891168 (by decide +kernel), [0]),
    (packed 17740265617453417743212560060155936
      17740265617453417743212560060155936 (by decide +kernel), [0, 0]),
    (packed 22255756089917247885745278738958368
      24892275101534057238314048894273568 (by decide +kernel), [1, 0]),
    (packed 22978883985993180636728849964697632
      27962058153478692044096880588097568 (by decide +kernel), [2, 0]),
    (packed 22884230703974010370441351171147808
      13494475753191259157577018101991456 (by decide +kernel), [3, 1, 3, 3, 2, 0]),
    (packed 22581116287950079340610394915112992
      11202634034112171575021556560562208 (by decide +kernel), [3, 3, 2, 3, 1, 0]),
    (packed 22538052261268209158440351968856096
      16004889401733664673175916058773536 (by decide +kernel), [3, 2, 3, 3, 0]),
    (packed 22489769660198694658371798831564832
      19926919891566173398240611930736672 (by decide +kernel), [3, 2, 3, 3, 1, 0]),
    (packed 22453050268928471392462583671162912
      12420898256453154516473586541660192 (by decide +kernel), [3, 3, 2, 3, 0]),
    (packed 22852781804489810799839963914864672
      7272095176193669210881269563918368 (by decide +kernel), [3, 3, 2, 1, 3, 0]),
    (packed 20146944983099834036853653608269856
      8620434523583009193481064382892064 (by decide +kernel), [3, 0, 0, 2]),
    (packed 22806646448576353192152333205080096
      23748787413519650650161438583687200 (by decide +kernel), [3, 1, 3, 3, 0]),
    (packed 18644930765349261608514054662916128
      18644930765349261608514054662916128 (by decide +kernel), [3, 2, 1, 3, 0]),
    (packed 9513264885904104040016395193845792
      19658114106476692182561598510106656 (by decide +kernel), [3, 1, 3, 2, 0, 0]),
    (packed 18359910197598529884369643395156000
      8407854939806122548181496560617504 (by decide +kernel), [3, 3, 1, 0]),
    (packed 18561539526256435391920881438132256
      15788731992045256177750067984730144 (by decide +kernel), [3, 1, 3, 2, 0]),
    (packed 7398547991451487267986502981388320
      27588612146144558575139404079695904 (by decide +kernel), [2, 1, 3, 1, 0]),
    (packed 22728237725033436153095829507967008
      9227794096546495382497070466730016 (by decide +kernel), [0, 0, 1, 0, 0, 0]),
    (packed 22374289970633997496708239128725536
      4192383850574162936088311257106464 (by decide +kernel), [2, 1, 0])]

private def pair3 : Level where
  point := 2
  lifts := [
    packed 12142329352256925737560884765690912
      10879746875111526014201489561556000 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 12142329352256925737560884765690912
      10879746875111526014201489561556000 (by decide +kernel), [0]),
    (packed 26298889071561161272808105626308640
      18809569672065262017736225409471520 (by decide +kernel), [1, 3, 0, 3]),
    (packed 27591865074298862094695313475933216
      13892907253669720738066406009508896 (by decide +kernel), [0, 4, 4, 0, 4]),
    (packed 22723077228102966558251015485429792
      11824063843853639990625654604895264 (by decide +kernel), [2, 1, 3, 2, 0, 2]),
    (packed 20214615873223735902859209456852000
      13693307226744951357107281047295008 (by decide +kernel), [3, 1, 0, 3]),
    (packed 28161420555530108010540297844301856
      28157310783193104679679786281735200 (by decide +kernel), [0, 3, 0, 2, 0, 1, 2, 0]),
    (packed 22599256871949215392215137356588064
      15067789834487886009270403111457824 (by decide +kernel), [1, 1, 4, 2, 1, 0, 2]),
    (packed 21516693371452385496898621391808544
      24154474695522259216113855514514464 (by decide +kernel), [4, 3, 1, 4, 4, 0]),
    (packed 26623447219801940309547655974104096
      12197985837763886293925630173123616 (by decide +kernel), [2, 4, 3, 1, 0]),
    (packed 13273104805563314461066618656731168
      4608557971007982509987343305449504 (by decide +kernel), [0, 2, 4, 3, 1, 0]),
    (packed 25117594822477630881709373705565216
      18432527506234861839969072331592736 (by decide +kernel), [4, 4, 1, 4, 1, 1, 0]),
    (packed 21284650946146325192739834764113952
      26310696605098395716231137665258528 (by decide +kernel), [0, 0, 4, 0, 3, 0]),
    (packed 17382862288162094139031387173960736
      8563629902077438684751756272047136 (by decide +kernel), [4, 2, 4, 1, 0, 3]),
    (packed 19605786751124688336799608807833632
      4404223420392584245757384797623328 (by decide +kernel), [1, 2, 1, 4, 1, 2, 0]),
    (packed 13723095298492062931023931017479200
      5702671151384429854989353991312416 (by decide +kernel), [3, 2, 1, 3, 2, 1, 0]),
    (packed 11899059097003663784756069059119136
      25279808103857296521978732758864928 (by decide +kernel), [3, 1, 2, 4, 2, 1, 0]),
    (packed 17349205055706834310886719965809696
      26092148266775101889726265955030048 (by decide +kernel), [1, 3, 1, 2, 4, 2, 0]),
    (packed 9540483854353830196388969921728544
      20204064566945632481446137479926816 (by decide +kernel), [4, 1, 3, 1, 0, 3]),
    (packed 13324920701530921323054118255940640
      13070048673240884379729512590971936 (by decide +kernel), [1, 2, 1, 3, 0, 3]),
    (packed 27487190317613587705270464994007072
      3498264254771072043267679265920032 (by decide +kernel), [3, 2, 1, 3, 0, 2])]

private def pair4 : Level where
  point := 0
  lifts := [
    packed 27837830884967958515780263127156737
      22983158015137777959272342021703681 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 27837830884967958515780263127156737
      22983158015137777959272342021703681 (by decide +kernel), [0])]

private def block0 : Level where
  point := 1
  lifts := [
    packed 29435102469747468020541888070160771
      29435102469747468020541888070160771 (by decide +kernel),
    packed 29434967107524823098911104328910406
      29434967107524823098911104328910406 (by decide +kernel),
    packed 29435304441351363498195551193891914
      29435304441351363498195551193891914 (by decide +kernel),
    packed 29435017774808905839674087284578833
      29435017774808905839674087284578833 (by decide +kernel)]
  reps := [
    (packed 29435409602188605818360983165741057
      29435409602188605818360983165741057 (by decide +kernel), [3, 2, 1]),
    (1, []),
    (packed 29435304441351363498195551193891914
      29435304441351363498195551193891914 (by decide +kernel), [2]),
    (packed 29435583953455144104154371096353900
      29435583953455144104154371096353900 (by decide +kernel), [3, 2, 1, 0]),
    (packed 29435497420975889931431760488640647
      29435497420975889931431760488640647 (by decide +kernel), [2, 0]),
    (packed 29435322696119192281003122935414994
      29435322696119192281003122935414994 (by decide +kernel), [3, 2]),
    (packed 29435534746558956885479779851111652
      29435534746558956885479779851111652 (by decide +kernel), [3, 1, 0]),
    (packed 29435381981851260144456858055344450
      29435381981851260144456858055344450 (by decide +kernel), [3, 1]),
    (packed 29434934962184772876145996484627821
      29434934962184772876145996484627821 (by decide +kernel), [3, 0]),
    (packed 29435102469747468020541888070160771
      29435102469747468020541888070160771 (by decide +kernel), [0]),
    (packed 29435248498295609032881291873761707
      29435248498295609032881291873761707 (by decide +kernel), [2, 1, 0]),
    (packed 29434861956352903257419016171632083
      29434861956352903257419016171632083 (by decide +kernel), [1, 0]),
    (packed 29435017774808905839674087284578833
      29435017774808905839674087284578833 (by decide +kernel), [3]),
    (packed 29435126751005855595796174905657904
      29435126751005855595796174905657904 (by decide +kernel), [2, 1]),
    (packed 29434967107524823098911104328910406
      29434967107524823098911104328910406 (by decide +kernel), [1]),
    (packed 29434890541403008480573726443253358
      29434890541403008480573726443253358 (by decide +kernel), [3, 2, 0])]

private def block1 : Level where
  point := 20
  lifts := [
    packed 26880781754364979604467285409511648
      28098883493816395243574450663402624 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 26880781754364979604467285409511648
      28098883493816395243574450663402624 (by decide +kernel), [0]),
    (packed 28098883493816395243574450663402624
      26880781754364979604467285409511648 (by decide +kernel), [0, 0])]

private def block2 : Level where
  point := 15
  lifts := [
    packed 26598303592678480101242731841896640
      26598303592678480101242731841896640 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 28171013657713305950029231005637732
      28171687742666331703648130770713011 (by decide +kernel), [1, 1, 0, 3, 1]),
    (packed 26598303592678480101242731841896640
      26598303592678480101242731841896640 (by decide +kernel), [0]),
    (packed 20309440768737675725268241606555076
      20309709138173945095810689976704107 (by decide +kernel), [1, 1, 0, 3, 1, 0])]

private def block3 : Level where
  point := 9
  lifts := [
    packed 27650514022438072166720624938929376
      12600544002479377469913096510846080 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 26353677838757378173396173851867750
      20310350536904937335714634515460557 (by decide +kernel), [4, 2, 1, 2, 2, 0]),
    (packed 19864220578091679234063316103179712
      26582056687504203274589275283892736 (by decide +kernel), [1, 0]),
    (packed 28941912968367779156040970045627745
      28942456920915108283496458352105485 (by decide +kernel), [2, 0, 1, 0, 3, 1]),
    (packed 27650514022438072166720624938929376
      12600544002479377469913096510846080 (by decide +kernel), [0])]

private def block4 : Level where
  point := 8
  lifts := [
    packed 20390576407724898669620548414770240
      28081280961133684188298778318538176 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 28090011164523578409863002486839360
      20390697565528096735528994084587008 (by decide +kernel), [0, 0, 1, 0, 0]),
    (packed 29435521785422271051858421961010368
      29435013571114582427275140443388480 (by decide +kernel), [0, 0, 1, 0, 0, 0]),
    (packed 20390576407724898669620548414770240
      28081280961133684188298778318538176 (by decide +kernel), [0]),
    (packed 11021126446001084928026285224445024
      26305547529094897208590231531469344 (by decide +kernel), [0, 0]),
    (packed 26305547529094897208590231531469344
      11021126446001084928026285224445024 (by decide +kernel), [0, 0, 0])]

private def block5 : Level where
  point := 5
  lifts := [
    packed 27482085820573748070708653474613280
      7394378777512557222885207143811104 (by decide +kernel)]
  reps := [
    (1, []),
    (packed 7313243668788779640149985275251139
      19822385062526216481080740102015501 (by decide +kernel), [5, 4, 1, 4, 3, 0, 0]),
    (packed 28162763527233357618162336180679744
      28171413403090535963610280131888352 (by decide +kernel), [0, 1, 0]),
    (packed 26820400942689681560294451290911137
      20351362020213926180122002614463504 (by decide +kernel), [2, 4, 1, 0, 5, 4, 2]),
    (packed 12602158263839635055152898016364641
      28077592307891766919431217184025616 (by decide +kernel), [3, 6, 0, 4, 1, 1, 2]),
    (packed 7394378777512557222885207143811104
      27482085820573748070708653474613280 (by decide +kernel), [0, 0]),
    (packed 27482085820573748070708653474613280
      7394378777512557222885207143811104 (by decide +kernel), [0])]

section

/- Representatives at successive levels multiply to enumerate the group.
Sifting checks membership in this enumeration by removing one representative
at a time, using the image of the current base point to select it. -/
variable {α : Type*}

private def enumerated : List (α × List (Perm α)) → List (Perm α)
  | [] => [1]
  | (_, rs) :: cs => rs.flatMap fun r => (enumerated cs).map (r * ·)

variable [DecidableEq α] [Fintype α] in
private def sift : List (α × List (Perm α)) → Perm α → Bool
  | [], g => decide (g = 1)
  | (x, rs) :: cs, g =>
    match rs.find? (fun r => r x == g x) with
    | none => false
    | some r => sift cs (r⁻¹ * g)

private theorem mem_enumerated_cons {g : Perm α} {x : α} {rs : List (Perm α)}
    {cs : List (α × List (Perm α))} :
    g ∈ enumerated ((x, rs) :: cs) ↔ ∃ r ∈ rs, ∃ h ∈ enumerated cs, r * h = g := by
  simp [enumerated, List.mem_flatMap, List.mem_map]

variable [DecidableEq α] [Fintype α] in
private theorem mem_enumerated_of_sift {cs : List (α × List (Perm α))} {g : Perm α}
    (h : sift cs g = true) : g ∈ enumerated cs := by
  induction cs generalizing g with
  | nil => simpa [sift, enumerated] using h
  | cons head cs ih =>
    obtain ⟨x, rs⟩ := head
    simp only [sift] at h
    split at h
    next => contradiction
    next r hr =>
      exact mem_enumerated_cons.mpr
        ⟨r, List.mem_of_find?_eq_some hr, r⁻¹ * g, ih h, by simp⟩

variable [DecidableEq α] [Fintype α] in
private theorem chain_enumerates {x : α} {rs gs : List (Perm α)}
    {cs : List (α × List (Perm α))} {K : Subgroup (Perm α)}
    (hK : ∀ g : Perm α, g ∈ enumerated cs ↔ g ∈ K)
    (hKgs : K ≤ Subgroup.closure {g | g ∈ gs})
    (hRgs : ∀ r ∈ rs, r ∈ Subgroup.closure {g | g ∈ gs})
    (hId : 1 ∈ rs)
    (hstep : ∀ g ∈ gs, ∀ r ∈ rs, sift ((x, rs) :: cs) (g * r) = true ∧
      sift ((x, rs) :: cs) (g⁻¹ * r) = true) :
    ∀ g : Perm α, g ∈ enumerated ((x, rs) :: cs) ↔
      g ∈ Subgroup.closure {g | g ∈ gs} := by
  intro g
  constructor
  · intro hg
    obtain ⟨r, hr, k, hk, rfl⟩ := mem_enumerated_cons.mp hg
    exact mul_mem (hRgs r hr) (hKgs ((hK k).1 hk))
  · intro hg
    refine Subgroup.closure_induction_left ?_ ?_ ?_ hg
    · exact mem_enumerated_cons.mpr ⟨1, hId, 1, (hK 1).2 K.one_mem, by simp⟩
    · intro a ha b _ hb
      obtain ⟨r, hr, k, hk, rfl⟩ := mem_enumerated_cons.mp hb
      obtain ⟨s, hs, l, hl, h⟩ := mem_enumerated_cons.mp
        (mem_enumerated_of_sift ((hstep a ha r hr).1))
      exact mem_enumerated_cons.mpr
        ⟨s, hs, l * k, (hK _).2 (mul_mem ((hK _).1 hl) ((hK _).1 hk)), by
          rw [← mul_assoc, h, mul_assoc]⟩
    · intro a ha b _ hb
      obtain ⟨r, hr, k, hk, rfl⟩ := mem_enumerated_cons.mp hb
      obtain ⟨s, hs, l, hl, h⟩ := mem_enumerated_cons.mp
        (mem_enumerated_of_sift ((hstep a ha r hr).2))
      exact mem_enumerated_cons.mpr
        ⟨s, hs, l * k, (hK _).2 (mul_mem ((hK _).1 hl) ((hK _).1 hk)), by
          rw [← mul_assoc, h, mul_assoc]⟩

private def generators (ls : List Level) : List P := ls.flatMap Level.lifts

private def subgroup (ls : List Level) : Subgroup P :=
  Subgroup.closure {g | g ∈ generators ls}

private def coords (ls : List Level) : List (Fin 23 × List P) :=
  ls.map fun l => (l.point, l.reps.map Prod.fst)

private def word (gs : List P) (w : List Nat) : P :=
  (w.map (gs[·]?.getD 1)).prod

private theorem word_mem (ls : List Level) (w : List Nat) :
    word (generators ls) w ∈ subgroup ls := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
    apply mul_mem _ ih
    change (generators ls)[i]?.getD 1 ∈ subgroup ls
    by_cases hi : i < (generators ls).length
    · rw [List.getElem?_eq_getElem hi, Option.getD_some]
      exact Subgroup.subset_closure (List.getElem_mem _)
    · rw [List.getElem?_eq_none (by omega), Option.getD_none]
      exact one_mem _

/- The tail generators fix the base point and the representatives have distinct
images there. The word and sifting checks certify closure of the enumeration
under left multiplication by the generators and their inverses. -/
private def validLevel (l : Level) (ls : List Level) : Bool :=
  let rs := l.reps.map Prod.fst
  let gs := generators (l :: ls)
  let cs := coords (l :: ls)
  decide ((rs.map (· l.point)).Nodup) &&
  rs.contains 1 &&
  (generators ls).all (fun g => g l.point == l.point) &&
  l.reps.all (fun (r, w) => r == word gs w) &&
  gs.all (fun g => rs.all (fun r => sift cs (g * r) && sift cs (g⁻¹ * r)))

private def validChain : List Level → Bool
  | [] => true
  | l :: ls => validLevel l ls && validChain ls

private theorem nodup_enumerated_cons {x : α} {rs : List (Perm α)}
    {cs : List (α × List (Perm α))}
    (hR : (rs.map (· x)).Nodup) (he : (enumerated cs).Nodup)
    (hfix : ∀ k ∈ enumerated cs, k x = x) :
    (enumerated ((x, rs) :: cs)).Nodup := by
  rw [enumerated, List.nodup_flatMap]
  refine ⟨fun r _ => he.map (mul_right_injective r), ?_⟩
  rw [List.Nodup, List.pairwise_map] at hR
  apply hR.imp
  intro r s hrs z hzr hzs
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hzr
  obtain ⟨a, ha, h⟩ := List.mem_map.mp hzs
  apply hrs
  simpa only [Perm.mul_apply, hfix a ha, hfix k hk] using congrArg (fun g : Perm α => g x) h.symm

end

private theorem subgroup_mono_cons (l : Level) (ls : List Level) :
    subgroup ls ≤ subgroup (l :: ls) := by
  apply Subgroup.closure_mono
  intro g hg
  change g ∈ l.lifts ++ generators ls
  exact List.mem_append_right _ hg

private theorem validChain_spec (ls : List Level) (h : validChain ls = true) :
    (∀ g, g ∈ enumerated (coords ls) ↔ g ∈ subgroup ls) ∧ (enumerated (coords ls)).Nodup := by
  induction ls with
  | nil =>
    simp [coords, enumerated, subgroup, generators]
  | cons l ls ih =>
    obtain ⟨hstep, htail⟩ := Bool.and_eq_true_iff.mp h
    specialize ih htail
    simp only [validLevel, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq] at hstep
    obtain ⟨⟨⟨⟨hR, hId⟩, hfix⟩, hwords⟩, hclosure⟩ := hstep
    have hRgs : ∀ r ∈ l.reps.map Prod.fst, r ∈ subgroup (l :: ls) := by
      intro r hr
      obtain ⟨⟨s, w⟩, hs, rfl⟩ := List.mem_map.mp hr
      exact (hwords (s, w) hs).symm ▸ word_mem _ _
    have hfix' : ∀ g ∈ enumerated (coords ls), g l.point = l.point := by
      intro g hg
      have h := (ih.1 g).mp hg
      apply Subgroup.closure_le (K := MulAction.stabilizer P l.point) |>.2 ?_ h
      exact hfix
    refine ⟨chain_enumerates ih.1 (subgroup_mono_cons l ls) hRgs ?_ ?_,
      nodup_enumerated_cons hR ih.2 hfix'⟩
    · simpa using hId
    · exact hclosure

private def pairChain := [pair4, pair3, pair2, pair1, pair0]
private def blockChain := [block5, block4, block3, block2, block1, block0]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 0 in
-- Kernel sifting checks the generator products for every representative in the chain.
private theorem pair_valid : validChain pairChain = true := by decide +kernel

set_option maxRecDepth 3000 in
set_option maxHeartbeats 0 in
-- Kernel sifting checks the generator products for every representative in the chain.
private theorem block_valid : validChain blockChain = true := by decide +kernel

private abbrev pairSimpleChain := [pair3, pair2, pair1, pair0]
private abbrev pointChain := [pair2, pair1, pair0]
private abbrev PairGroup := subgroup pairChain
private abbrev PairSimple := subgroup pairSimpleChain
private abbrev PointGroup := subgroup pointChain
private abbrev BlockGroup := subgroup blockChain

private theorem rep_mem (l : Level) (ls : List Level) (h : validLevel l ls = true)
    {r : P} (hr : r ∈ l.reps.map Prod.fst) : r ∈ subgroup (l :: ls) := by
  simp only [validLevel, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨s, w⟩, hs, rfl⟩ := List.mem_map.mp hr
  exact (h.1.2 (s, w) hs).symm ▸ word_mem _ _

private theorem tail_fixed {l : Level} {ls : List Level} (h : validLevel l ls = true) :
    subgroup ls ≤ MulAction.stabilizer P l.point := by
  simp only [validLevel, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  apply (Subgroup.closure_le _).mpr
  exact h.1.1.2

private theorem tail_eq_stabilizer {l : Level} {ls : List Level}
    (h : validChain (l :: ls) = true) :
    subgroup ls = subgroup (l :: ls) ⊓ MulAction.stabilizer P l.point := by
  obtain ⟨hl, ht⟩ := Bool.and_eq_true_iff.mp h
  apply le_antisymm (le_inf (subgroup_mono_cons l ls) (tail_fixed hl))
  intro p hp
  obtain ⟨r, hr, k, hk, rfl⟩ := mem_enumerated_cons.mp ((validChain_spec _ h).1 p |>.mpr hp.1)
  have hk' := ((validChain_spec _ ht).1 k).mp hk
  have hfix : k l.point = l.point := tail_fixed hl hk'
  have hst : r (k l.point) = l.point := hp.2
  rw [hfix] at hst
  simp only [validLevel, Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hl
  have hnodup := hl.1.1.1.1
  have hinj := (List.nodup_map_iff_inj_on (List.Nodup.of_map _ hnodup)).mp hnodup
  have h1 : (1 : P) ∈ l.reps.map Prod.fst := hl.1.1.1.2
  have hr1 : r = 1 := hinj r hr 1 h1 hst
  simpa [hr1] using hk'

private theorem simple_valid : validChain pairSimpleChain = true := by
  exact (Bool.and_eq_true_iff.mp pair_valid).2

private theorem point_valid : validChain pointChain = true := by
  exact (Bool.and_eq_true_iff.mp simple_valid).2

/- The first group preserves a pair and its pointwise stabilizer acts
2-transitively on the other 21 points. The second group preserves a heptad
and has a nontrivial abelian pointwise stabilizer. -/
private def preserving (s : Finset (Fin 23)) : Subgroup P where
  carrier := {g | ∀ i, g i ∈ s ↔ i ∈ s}
  one_mem' := by simp
  mul_mem' {a b} ha hb := fun i => (ha (b i)).trans (hb i)
  inv_mem' {a} ha := fun i => by simpa using (ha (a⁻¹ i)).symm

private theorem preserves_of_test (ls : List Level) (s : Finset (Fin 23))
    (h : (generators ls).all (fun g => decide (∀ i, g i ∈ s ↔ i ∈ s)) = true) :
    subgroup ls ≤ preserving s := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  change ∀ i, g i ∈ s ↔ i ∈ s
  exact of_decide_eq_true (List.all_eq_true.mp h g hg)

private def binarySet : Finset (Fin 23) := {0, 1}
private def heptad : Finset (Fin 23) := {5, 8, 9, 15, 20, 21, 22}

private theorem pair_preserves : PairGroup ≤ preserving binarySet :=
  preserves_of_test _ _ (by decide +kernel)

private theorem block_preserves : BlockGroup ≤ preserving heptad :=
  preserves_of_test _ _ (by decide +kernel)

private theorem pair_fixed (g : PairSimple) : (g : P) 0 = 0 ∧ (g : P) 1 = 1 := by
  have hmem := (subgroup_mono_cons pair4 pairSimpleChain) g.2
  have h0 : (g : P) 0 = 0 := tail_fixed ((Bool.and_eq_true_iff.mp pair_valid).1) g.2
  have h1 := (pair_preserves hmem) (1 : Fin 23)
  change (g : P) 1 ∈ binarySet ↔ (1 : Fin 23) ∈ binarySet at h1
  have hne : (g : P) 1 ≠ 0 := fun h => by
    rw [← h0] at h
    exact one_ne_zero (g.val.injective h)
  refine ⟨h0, ?_⟩
  simpa [binarySet, hne] using h1.mpr (by simp [binarySet])

private def ChainPoint := {i : Fin 23 // i ∉ binarySet}

private instance pairSimpleAction : MulAction PairSimple ChainPoint where
  smul g x := ⟨(g : P) x.1, fun h => x.2 ((pair_preserves
    (subgroup_mono_cons pair4 pairSimpleChain g.2)) x.1 |>.mp h)⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private def firstPoint : ChainPoint := ⟨2, by decide⟩
private def secondPoint : ChainPoint := ⟨3, by decide⟩

private theorem reach_from (l : Level) (ls : List Level)
    (hl : validLevel l ls = true) {i : Fin 23}
    (hi : (l.reps.map fun r => r.1 l.point).contains i = true) :
    ∃ g : subgroup (l :: ls), (g : P) l.point = i := by
  rw [List.contains_eq_mem, decide_eq_true_eq] at hi
  obtain ⟨⟨r, w⟩, hr, he⟩ := List.mem_map.mp hi
  exact ⟨⟨r, rep_mem _ _ hl (List.mem_map.mpr ⟨(r, w), hr, rfl⟩)⟩, he⟩

private theorem point_reachable (x : ChainPoint) :
    ∃ g : PairSimple, g • firstPoint = x := by
  have cover : ∀ i : Fin 23, i ∉ binarySet →
      (pair3.reps.map (fun r => r.1 pair3.point)).contains i = true := by decide +kernel
  obtain ⟨g, hg⟩ := reach_from pair3 pointChain ((Bool.and_eq_true_iff.mp simple_valid).1)
    (cover x.1 x.2)
  exact ⟨g, Subtype.ext hg⟩

private theorem second_reachable (x : ChainPoint) (hx : x ≠ firstPoint) :
    ∃ g : PairSimple, g • firstPoint = firstPoint ∧ g • secondPoint = x := by
  have cover : ∀ i : Fin 23, i ∉ binarySet → i ≠ 2 →
      (pair2.reps.map (fun r => r.1 pair2.point)).contains i = true := by decide +kernel
  obtain ⟨g, hg⟩ := reach_from pair2 [pair1, pair0] ((Bool.and_eq_true_iff.mp point_valid).1)
    (cover x.1 x.2 (fun h => hx (Subtype.ext h)))
  exact ⟨⟨g.1, subgroup_mono_cons pair3 pointChain g.2⟩,
    Subtype.ext (tail_fixed (Bool.and_eq_true_iff.mp simple_valid).1 g.2), Subtype.ext hg⟩

private theorem two_transitive : MulAction.IsMultiplyPretransitive PairSimple ChainPoint 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  have origin (x y : ChainPoint) (h : x ≠ y) :
      ∃ g : PairSimple, g • firstPoint = x ∧ g • secondPoint = y := by
    obtain ⟨p, hp⟩ := point_reachable x
    obtain ⟨q, hq, hq'⟩ := second_reachable (p⁻¹ • y) (by
      intro he
      exact h (hp.symm.trans ((inv_smul_eq_iff.mp he).symm)))
    exact ⟨p*q, by simp [mul_smul, hq, hp], by simp [mul_smul, hq']⟩
  intro a b c d hab hcd
  obtain ⟨p, hp, hp'⟩ := origin a b hab
  obtain ⟨q, hq, hq'⟩ := origin c d hcd
  exact ⟨q*p⁻¹, by simp [mul_smul, ← hp, hq], by simp [mul_smul, ← hp', hq']⟩

private theorem simple_faithful : FaithfulSMul PairSimple ChainPoint := by
  refine ⟨fun {g h} he => Subtype.ext (Equiv.ext fun i => ?_)⟩
  by_cases hi : i ∈ binarySet
  · rcases (show i = 0 ∨ i = 1 by simpa [binarySet] using hi) with rfl | rfl
    · exact (pair_fixed g).1.trans (pair_fixed h).1.symm
    · exact (pair_fixed g).2.trans (pair_fixed h).2.symm
  · exact congrArg Subtype.val (he ⟨i, hi⟩)

private abbrev fixing (s : Finset (Fin 23)) : Subgroup P :=
  fixingSubgroup P (s : Set (Fin 23))

private theorem mem_fixing {s : Finset (Fin 23)} {g : P} :
    g ∈ fixing s ↔ ∀ i ∈ s, g i = i :=
  mem_fixingSubgroup_iff P

private theorem fixing_normal {G : Subgroup P} {s : Finset (Fin 23)}
    (h : G ≤ preserving s) : ((fixing s).subgroupOf G).Normal := by
  constructor
  intro n hn g
  change ((g : P) * (n : P) * (g : P)⁻¹) ∈ fixing s
  have hfix := (mem_fixing (g := (n : P))).mp hn
  apply mem_fixing.mpr
  intro i hi
  have hgi := (h (inv_mem g.property)) i |>.mpr hi
  change (g : P) ((n : P) ((g : P)⁻¹ i)) = i
  rw [hfix _ hgi]
  exact g.val.apply_symm_apply i

private theorem group_fixes_of_test (ls : List Level) (s : List (Fin 23))
    (h : (generators ls).all (fun g => s.all (fun i => g i == i)) = true) :
    subgroup ls ≤ fixing s.toFinset := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  apply mem_fixing.mpr
  intro i hi
  exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp h g hg) i (by simpa using hi))

private def PairSocle := (fixing binarySet).subgroupOf PairGroup

private theorem pairSimple_eq : PairSimple = PairGroup ⊓ fixing binarySet := by
  refine le_antisymm (le_inf (subgroup_mono_cons pair4 pairSimpleChain) ?_) ?_
  · intro g hg
    rw [mem_fixing]
    intro i hi
    rcases (show i = 0 ∨ i = 1 by simpa [binarySet] using hi) with rfl | rfl
    · exact (pair_fixed ⟨g, hg⟩).1
    · exact (pair_fixed ⟨g, hg⟩).2
  · intro g hg
    change g ∈ subgroup pairSimpleChain
    rw [tail_eq_stabilizer pair_valid]
    exact ⟨hg.1, (mem_fixing.mp hg.2) 0 (by decide)⟩

private def pairSocleEquiv : PairSimple ≃* PairSocle where
  toFun g := ⟨⟨g.1, (le_inf_iff.mp pairSimple_eq.le).1 g.2⟩, (le_inf_iff.mp pairSimple_eq.le).2 g.2⟩
  invFun g := ⟨g.1.1, pairSimple_eq.ge ⟨g.1.2, g.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private instance pairSocleNormal : PairSocle.Normal := fixing_normal pair_preserves

private theorem no_single_swap : Equiv.swap (0 : Fin 23) 1 ∉ PairGroup := by
  have h : PairGroup ≤ alternatingGroup (Fin 23) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    have he : (generators pairChain).all (fun g => decide (Equiv.Perm.sign g = 1)) = true :=
      by decide +kernel
    change Equiv.Perm.sign g = 1
    exact of_decide_eq_true (List.all_eq_true.mp he g hg)
  intro he
  simpa using h he

private theorem pair_centralizer : Subgroup.centralizer (PairSocle : Set PairGroup) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have commutes (s : PairSimple) : (g : P) * (s : P) = (s : P) * (g : P) := by
    have h := (Subgroup.mem_centralizer_iff.mp hg) (pairSocleEquiv s).1 (pairSocleEquiv s).2
    exact congrArg Subtype.val h.symm
  have pres := pair_preserves g.2
  have fix (i : Fin 23) (hi : i ∉ binarySet) : (g : P) i = i := by
    by_contra h
    let b : ChainPoint := ⟨i, hi⟩
    let c : ChainPoint := ⟨(g : P) i, fun hc => hi ((pres i).mp hc)⟩
    obtain ⟨d, hd, hdc⟩ : ∃ d : ChainPoint, d ≠ b ∧ d ≠ c := by
      have hc : ∀ i j : Fin 23, ∃ k : Fin 23, k ∉ binarySet ∧ k ≠ i ∧ k ≠ j := by decide +kernel
      obtain ⟨k, hk, hb, hc⟩ := hc i ((g : P) i)
      exact ⟨⟨k, hk⟩, fun e => hb (congrArg Subtype.val e), fun e => hc (congrArg Subtype.val e)⟩
    obtain ⟨s, hs, hsc⟩ := (MulAction.is_two_pretransitive_iff.mp two_transitive)
      (show b ≠ c from fun e => h (congrArg Subtype.val e).symm) hd.symm
    have hs0 : (s : P) i = i := congrArg Subtype.val hs
    have hsc0 : (s : P) ((g : P) i) = d.val := congrArg Subtype.val hsc
    have he := congrArg (fun p : P => p i) (commutes s)
    simp only [Perm.mul_apply, hs0, hsc0] at he
    exact hdc (Subtype.ext he.symm)
  have gpair (i : Fin 23) (hi : i ∈ binarySet) : (g : P) i = 0 ∨ (g : P) i = 1 := by
    simpa [binarySet] using (pres i).mpr hi
  by_cases h0 : (g : P) 0 = 0
  · have h1 : (g : P) 1 = 1 := (gpair 1 (by decide)).resolve_left fun e =>
      one_ne_zero (g.val.injective (e.trans h0.symm))
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ binarySet
    · rcases (show i = 0 ∨ i = 1 by simpa [binarySet] using hi) with rfl | rfl
      · exact h0
      · exact h1
    · exact fix i hi
  · have h0' := (gpair 0 (by decide)).resolve_left h0
    have h1 : (g : P) 1 = 0 := (gpair 1 (by decide)).resolve_right fun e =>
      one_ne_zero (g.val.injective (e.trans h0'.symm))
    have he : (g : P) = Equiv.swap 0 1 := by
      apply Equiv.ext
      intro i
      by_cases hi : i ∈ binarySet
      · rcases (show i = 0 ∨ i = 1 by simpa [binarySet] using hi) with rfl | rfl
        · simpa using h0'
        · simpa using h1
      · have hi0 : i ≠ 0 := fun h => hi (h ▸ by decide)
        have hi1 : i ≠ 1 := fun h => hi (h ▸ by decide)
        rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
        exact fix i hi
    exact False.elim (no_single_swap (he ▸ g.2))

private def BlockKernel := (fixing heptad).subgroupOf BlockGroup

private instance blockKernelNormal : BlockKernel.Normal := fixing_normal block_preserves

private theorem blockKernel_eq : subgroup [block0] = BlockGroup ⊓ fixing heptad := by
  refine le_antisymm
    (le_inf ?_ (group_fixes_of_test _ [5, 8, 9, 15, 20, 21, 22] (by decide +kernel))) ?_
  · exact (subgroup_mono_cons block1 _).trans ((subgroup_mono_cons block2 _).trans
      ((subgroup_mono_cons block3 _).trans ((subgroup_mono_cons block4 _).trans
        (subgroup_mono_cons block5 _))))
  · intro g hg
    have h5 : g ∈ subgroup [block4, block3, block2, block1, block0] := by
      rw [tail_eq_stabilizer block_valid]
      exact ⟨hg.1, mem_fixing.mp hg.2 _ (by decide)⟩
    have h4 : g ∈ subgroup [block3, block2, block1, block0] := by
      rw [tail_eq_stabilizer ((Bool.and_eq_true_iff.mp block_valid).2)]
      exact ⟨h5, mem_fixing.mp hg.2 _ (by decide)⟩
    have h3 : g ∈ subgroup [block2, block1, block0] := by
      rw [tail_eq_stabilizer ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp block_valid).2).2)]
      exact ⟨h4, mem_fixing.mp hg.2 _ (by decide)⟩
    have hrest : validChain [block2, block1, block0] = true := by
      have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp block_valid).2).2
      exact (Bool.and_eq_true_iff.mp h).2
    have h2 : g ∈ subgroup [block1, block0] := by
      rw [tail_eq_stabilizer hrest]
      exact ⟨h3, mem_fixing.mp hg.2 _ (by decide)⟩
    rw [tail_eq_stabilizer ((Bool.and_eq_true_iff.mp hrest).2)]
    exact ⟨h2, mem_fixing.mp hg.2 _ (by decide)⟩

private theorem abelian_closure {gs : List P}
    (h : gs.all (fun a => gs.all (fun b => decide (a * b = b * a))) = true) :
    IsMulCommutative (Subgroup.closure {g | g ∈ gs}) :=
  Subgroup.isMulCommutative_closure fun a ha b hb _ =>
    show a * b = b * a from
      of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb)

private instance blockKernelCommutative : IsMulCommutative BlockKernel := by
  have : IsMulCommutative (subgroup [block0]) := abelian_closure (by decide +kernel)
  apply IsMulCommutative.of_setLike_mul_comm
  intro x hx y hy
  apply Subtype.ext
  exact setLike_mul_comm (blockKernel_eq.ge ⟨x.2, hx⟩) (blockKernel_eq.ge ⟨y.2, hy⟩)

private theorem blockKernel_ne_bot : BlockKernel ≠ ⊥ := by
  have h : ((generators [block0])[0]?.getD 1) ∈ subgroup [block0] :=
    by simpa [word] using word_mem [block0] [0]
  have he : (generators [block0])[0]?.getD 1 ≠ 1 := by decide +kernel
  have h' := blockKernel_eq.le h
  let p : BlockGroup := ⟨_, h'.1⟩
  intro hbot
  have hp : p ∈ BlockKernel := h'.2
  rw [hbot, Subgroup.mem_bot] at hp
  exact he (congrArg Subtype.val hp)
/- Iwasawa's argument applies to an abelian subgroup normalized by a point
stabilizer. Normal generation together with containment in the commutator
supplies the perfection hypothesis. -/
private theorem simple_of_normal_generation {G X : Type*} [Group G] [Nontrivial G]
    [MulAction G X] [MulAction.IsQuasiPreprimitive G X] (hfaithful : FaithfulSMul G X)
    (a : X) (T : Subgroup G) [IsMulCommutative T]
    (hstab : MulAction.stabilizer G a ≤ Subgroup.normalizer T)
    (hgen : Subgroup.normalClosure (T : Set G) = ⊤)
    (hperf : T ≤ commutator G) :
    IsSimpleGroup G := by
  have perfect : commutator G = ⊤ :=
    top_unique (hgen ▸ Subgroup.normalClosure_le_normal hperf)
  refine ⟨fun N hN => ?_⟩
  by_cases hF : MulAction.fixedPoints N X = Set.univ
  · left
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro n hn
    apply hfaithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp hF x ⟨n, hn⟩
  · right
    have htrans := MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hF
    have hsup : N ⊔ T = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.normalClosure, Subgroup.closure_le]
      intro x hx
      obtain ⟨t, ht, ht'⟩ := (Group.mem_conjugatesOfSet_iff).mp hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp ht'
      obtain ⟨n, hn⟩ := htrans.exists_smul_eq a (g • a)
      have hk : (n : G)⁻¹ * g ∈ MulAction.stabilizer G a := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, ← hn]
        exact inv_smul_smul (n : G) a
      have hkt : ((n : G)⁻¹ * g) * t * ((n : G)⁻¹ * g)⁻¹ ∈ T :=
        (hstab hk t).mp ht
      have hn' : (n : G) ∈ N ⊔ T := Subgroup.mem_sup_left n.2
      change _ ∈ N ⊔ T
      convert mul_mem (mul_mem hn' (Subgroup.mem_sup_right hkt)) (inv_mem hn') using 1
      group
    exact top_unique (perfect ▸ Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup)

private def conjAction {G : Type*} [Group G] (S : Subgroup G) [S.Normal] :
    G →* MulAut S :=
  S.normalizerMonoidHom.comp
    (Subgroup.inclusion (by rw [Subgroup.normalizer_eq_top] :
      (⊤ : Subgroup G) ≤ Subgroup.normalizer (S : Set G)))
    |>.comp Subgroup.topEquiv.symm.toMonoidHom

private theorem conjAction_apply {G : Type*} [Group G] (S : Subgroup G) [S.Normal]
    (g : G) (s : S) : ((conjAction S g s : S) : G) = g * s * g⁻¹ := rfl

private theorem conjAction_injective {G : Type*} [Group G] (S : Subgroup G) [S.Normal]
    (hcen : Subgroup.centralizer (S : Set G) = ⊥) : Function.Injective (conjAction S) := by
  apply (injective_iff_map_eq_one (conjAction S)).mpr
  intro g hg
  have hmem : g ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have e := DFunLike.congr_fun hg ⟨s, hs⟩
    have e' : g * s * g⁻¹ = s := congrArg Subtype.val e
    exact eq_mul_inv_iff_mul_eq.mp e'.symm
  simpa [hcen] using hmem

private theorem no_abelian_normal {G : Type*} [Group G] (S : Subgroup G) [S.Normal]
    [IsSimpleGroup S] (hnoncomm : ¬ IsMulCommutative S)
    (hcen : Subgroup.centralizer (S : Set G) = ⊥) (N : Subgroup G)
    [N.Normal] [IsMulCommutative N] : N = ⊥ := by
  rcases (show N.subgroupOf S = ⊥ ∨ N.subgroupOf S = ⊤ from
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _) with h | h
  · have hinf : N ⊓ S = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      have hmem : (⟨g, hg.2⟩ : S) ∈ N.subgroupOf S := hg.1
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    have hle : N ≤ Subgroup.centralizer (S : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact le_bot_iff.mp (hinf ▸ (Subgroup.commutator_le_inf N S))
    simpa [hcen] using hle
  · exfalso
    apply hnoncomm
    have hle : S ≤ N := fun g hg => show (⟨g, hg⟩ : S) ∈ N.subgroupOf S by simp [h]
    exact IsMulCommutative.of_setLike_mul_comm fun _ hx _ hy => setLike_mul_comm (hle hx) (hle hy)

/- These data give the abelian subgroup used in Iwasawa's argument for the
pointwise pair stabilizer. Words in conjugates recover its generators and
the supplied commutators recover the generators of the abelian subgroup. -/
private def radicalGenerators : List P := [
  packed 21066070898969451620813713620174880
    21066070898969451620813713620174880 (by decide +kernel),
  packed 17130054139679784263161636991371296
    17130054139679784263161636991371296 (by decide +kernel),
  packed 28820329111755796455432788379863072
    28820329111755796455432788379863072 (by decide +kernel),
  packed 29341886519044415565869421682952224
    29341886519044415565869421682952224 (by decide +kernel)]

private def conjugatePairs : List (P × P) := [
  (packed 3416643228142634634802433778762784
    13250967211719113798433917130692640 (by decide +kernel),
   packed 29341886519044415565869421682952224
     29341886519044415565869421682952224 (by decide +kernel)),
  (packed 3231582668564904357019976541541408
    22883091538192719983976413073528864 (by decide +kernel),
   packed 29341886519044415565869421682952224
     29341886519044415565869421682952224 (by decide +kernel)),
  (packed 22843471876317667251714472853181472
    18641638546000745020777047391745056 (by decide +kernel),
   packed 29341886519044415565869421682952224
     29341886519044415565869421682952224 (by decide +kernel)),
  (packed 6680898094532035171741801570911264
    26536188150773426144401727654641696 (by decide +kernel),
   packed 29341886519044415565869421682952224
     29341886519044415565869421682952224 (by decide +kernel)),
  (packed 23613133480433837454418674891566112
    4359834725175745182855430199194656 (by decide +kernel),
   packed 29341886519044415565869421682952224
     29341886519044415565869421682952224 (by decide +kernel)),
  (packed 20147528154612167052801007934444576
    7323987851941011900268575253408800 (by decide +kernel),
   packed 29341886519044415565869421682952224
     29341886519044415565869421682952224 (by decide +kernel))]

private def normalWords : List (List Nat) :=
  [[5, 4, 3, 2, 1, 4, 1], [3, 2, 4, 3, 4, 0], [0], [1], [4, 0, 4, 2, 1, 4, 0]]

private def commutatorPairs : List (P × P) := [
  (packed 8425184840837959030557287093045280
    26618308603368029062866912492947488 (by decide +kernel),
   packed 17130054139679784263161636991371296
     17130054139679784263161636991371296 (by decide +kernel)),
  (packed 8425184840837959030557287093045280
    26618308603368029062866912492947488 (by decide +kernel),
   packed 5982885655848120470344932700293152
     5982885655848120470344932700293152 (by decide +kernel)),
  (packed 8425184840837959030557287093045280
    26618308603368029062866912492947488 (by decide +kernel),
   packed 21640829824795307529570713222023200
     21640829824795307529570713222023200 (by decide +kernel)),
  (packed 8425184840837959030557287093045280
    26618308603368029062866912492947488 (by decide +kernel),
   packed 17740265617453417743212560060155936
     17740265617453417743212560060155936 (by decide +kernel))]

private def radicalAmbient : Subgroup P := Subgroup.closure {g | g ∈ radicalGenerators}
private def Radical := radicalAmbient.subgroupOf PairSimple

private theorem sift_mem {ls : List Level} (hl : validChain ls = true) {g : P}
    (hg : sift (coords ls) g = true) : g ∈ subgroup ls :=
  (validChain_spec ls hl).1 g |>.mp (mem_enumerated_of_sift hg)

private theorem radical_le : radicalAmbient ≤ PairSimple := by
  apply (Subgroup.closure_le PairSimple).mpr
  intro g hg
  have h : radicalGenerators.all (sift (coords pairSimpleChain)) = true := by decide +kernel
  exact sift_mem simple_valid (List.all_eq_true.mp h g hg)

private instance radicalAmbientCommutative : IsMulCommutative radicalAmbient :=
  abelian_closure (by decide +kernel)

private instance radicalCommutative : IsMulCommutative Radical :=
  Subgroup.subgroupOf_isMulCommutative _ _

private theorem words_in_subgroup {gs : List P} {K : Subgroup P}
    (hg : ∀ g ∈ gs, g ∈ K) (w : List Nat) : word gs w ∈ K := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
    apply mul_mem _ ih
    change gs[i]?.getD 1 ∈ K
    by_cases hi : i < gs.length
    · rw [List.getElem?_eq_getElem hi, Option.getD_some]
      exact hg _ (List.getElem_mem _)
    · rw [List.getElem?_eq_none (by omega), Option.getD_none]
      exact one_mem _

private def radicalWords : List P :=
  (List.range 16).map fun i => word radicalGenerators ((List.range 4).filter i.testBit)

private theorem radicalWords_mem {g : P} (hg : g ∈ radicalWords) : g ∈ radicalAmbient := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  exact words_in_subgroup (fun _ h => Subgroup.subset_closure h) _

private theorem conjugate_into_radical {g : P}
    (h : ∀ t ∈ radicalGenerators, g * t * g⁻¹ ∈ radicalAmbient) :
    ∀ t ∈ radicalAmbient, g * t * g⁻¹ ∈ radicalAmbient := by
  apply (Subgroup.closure_le (radicalAmbient.comap (MulAut.conj g).toMonoidHom)).mpr
  exact h

private theorem point_normalizes : PointGroup ≤ Subgroup.normalizer (radicalAmbient : Set P) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  have cert : (generators pointChain).all (fun g => radicalGenerators.all (fun t =>
      radicalWords.contains (g * t * g⁻¹) && radicalWords.contains (g⁻¹ * t * g))) = true :=
    by decide +kernel
  have facts (t) (ht : t ∈ radicalGenerators) :=
    Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp cert g hg) t ht)
  change g ∈ Subgroup.normalizer (radicalAmbient : Set P)
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · apply conjugate_into_radical
    intro a ha
    apply radicalWords_mem
    simpa only [List.contains_eq_mem, decide_eq_true_eq] using (facts a ha).1
  · intro ht
    have hi : g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ ∈ radicalAmbient :=
      conjugate_into_radical (g := g⁻¹) (fun a ha => radicalWords_mem (by
        simpa only [inv_inv, List.contains_eq_mem, decide_eq_true_eq] using (facts a ha).2)) _ ht
    simpa [mul_assoc] using hi

private theorem point_stabilizer_normalizes :
    MulAction.stabilizer PairSimple firstPoint ≤
      Subgroup.normalizer (Radical : Set PairSimple) := by
  apply (Subgroup.le_normalizer_iff).mpr
  intro g hg t ht
  have hg' : (g : P) ∈ PointGroup := by
    change (g : P) ∈ subgroup pointChain
    rw [tail_eq_stabilizer simple_valid]
    exact ⟨g.2, congrArg Subtype.val hg⟩
  exact (point_normalizes hg' (t : P)).mp ht

private theorem mapped_mem {K : Subgroup PairSimple} {g : PairSimple}
    (hg : (g : P) ∈ K.map PairSimple.subtype) : g ∈ K := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp hg
  exact (Subtype.ext he : u = g) ▸ hu

private theorem radical_normal_generates :
    Subgroup.normalClosure (Radical : Set PairSimple) = ⊤ := by
  apply top_unique
  intro g _
  apply mapped_mem
  let K := (Subgroup.normalClosure (Radical : Set PairSimple)).map PairSimple.subtype
  change (g : P) ∈ K
  have incl : PairSimple ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    let ps := conjugatePairs.map fun (g, t) => g * t * g⁻¹
    have hwords : normalWords.map (word ps) = generators pairSimpleChain := by decide +kernel
    rw [← hwords] at hp
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hp
    apply words_in_subgroup _ w
    intro u hu
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hu
    have hc : conjugatePairs.all (fun (a, b) =>
        sift (coords pairSimpleChain) a && radicalGenerators.contains b) = true :=
      by decide +kernel
    have h := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc _ hab)
    have ha := sift_mem simple_valid h.1
    have hb0 : b ∈ radicalGenerators := by
      simpa only [List.contains_eq_mem, decide_eq_true_eq] using h.2
    have hb : b ∈ radicalAmbient := Subgroup.subset_closure hb0
    let a' : PairSimple := ⟨a, ha⟩
    let b' : PairSimple := ⟨b, radical_le hb⟩
    refine Subgroup.mem_map.mpr ⟨a' * b' * a'⁻¹, ?_, rfl⟩
    exact Subgroup.conjugatesOfSet_subset_normalClosure
      (Group.conj_mem_conjugatesOfSet (Group.mem_conjugatesOfSet_iff.mpr
        ⟨b', hb, IsConj.refl _⟩))
  exact incl g.2

open scoped commutatorElement in
private theorem radical_in_commutator : Radical ≤ commutator PairSimple := by
  intro g hg
  apply mapped_mem
  have incl : radicalAmbient ≤ (commutator PairSimple).map PairSimple.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    have hpairs : commutatorPairs.map (fun (a, b) => ⁅a, b⁆) = radicalGenerators :=
      by decide +kernel
    rw [← hpairs] at hp
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hp
    have hc : commutatorPairs.all (fun (a, b) =>
        sift (coords pairSimpleChain) a && sift (coords pairSimpleChain) b) = true :=
      by decide +kernel
    have h := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc _ hab)
    let a' : PairSimple := ⟨a, sift_mem simple_valid h.1⟩
    let b' : PairSimple := ⟨b, sift_mem simple_valid h.2⟩
    exact Subgroup.mem_map.mpr ⟨⁅a', b'⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), rfl⟩
  exact incl hg

private theorem pairSimple_nontrivial : Nontrivial PairSimple := by
  obtain ⟨g, hg⟩ := point_reachable secondPoint
  refine ⟨⟨g, 1,?_⟩⟩
  rintro rfl
  have h : firstPoint = secondPoint := (one_smul _ _).symm.trans hg
  exact (by decide : (2 : Fin 23) ≠ 3) (congrArg Subtype.val h)

private theorem pairSimple_simple : IsSimpleGroup PairSimple := by
  let := pairSimple_nontrivial
  let := MulAction.isPreprimitive_of_is_two_pretransitive two_transitive
  exact simple_of_normal_generation simple_faithful firstPoint Radical point_stabilizer_normalizes
    radical_normal_generates radical_in_commutator

private theorem pairSimple_noncomm : ¬ IsMulCommutative PairSimple := by
  intro h
  let := pairSimple_nontrivial
  have h0 : commutator PairSimple = ⊥ := by
    rw [commutator_def, Subgroup.commutator_self_eq_bot_iff]
    infer_instance
  have hp : commutator PairSimple = ⊤ :=
    top_unique (radical_normal_generates ▸ Subgroup.normalClosure_le_normal radical_in_commutator)
  exact bot_ne_top (h0.symm.trans hp)
/- Compute permutation order as the least common multiple of cycle lengths.
A bit mask records points whose cycles have already been included. -/
open Function

private def step (p : P) (a : Fin 23) : Nat → Fin 23 → Nat → Nat × Nat
  | 0, _, bits => (0, bits)
  | n+1, x, bits =>
    let bits := (1 <<< x.val) ||| bits
    if p x = a then (1, bits) else
      let (d, bits) := step p a n (p x) bits
      (d + 1, bits)

private theorem step_fst (p : P) (a : Fin 23) {n k : Nat}
    (hk : k < minimalPeriod p a) (hn : minimalPeriod p a ≤ k + n) (b : Nat) :
    (step p a n (p^[k] a) b).1 = minimalPeriod p a - k := by
  induction n generalizing k b with
  | zero => omega
  | succ n ih =>
    simp only [step, ← Function.iterate_succ_apply']
    by_cases h : k + 1 = minimalPeriod p a
    · have he : (p : Fin 23 → Fin 23)^[k.succ] a = a := by
        rw [show k.succ = minimalPeriod p a from h, iterate_minimalPeriod]
      rw [ite_eq_left he]
      omega
    · have hlt : k + 1 < minimalPeriod p a := by omega
      have hne : (p : Fin 23 → Fin 23)^[k+1] a ≠ a := by
        intro hfix
        have he := (show IsPeriodicPt p (k+1) a from hfix).minimalPeriod_dvd
        exact not_le_of_gt hlt (Nat.le_of_dvd (Nat.succ_pos k) he)
      rw [ite_eq_right hne]
      change (step p a n (p^[k+1] a) ((1 <<< (p^[k] a).val) ||| b)).1 + 1 = _
      rw [ih hlt (by omega)]
      omega

private theorem step_bits (p : P) (a x y : Fin 23) (n b : Nat) :
    ((step p a n x b).2).testBit y.val = true →
      b.testBit y.val = true ∨ ∃ k, (p : Fin 23 → Fin 23)^[k] x = y := by
  induction n generalizing x b with
  | zero => exact Or.inl
  | succ n ih =>
    have mark (h : (((1 <<< x.val) ||| b).testBit y.val) = true) :
        b.testBit y.val = true ∨ ∃ k, (p : Fin 23 → Fin 23)^[k] x = y := by
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true] at h
      rcases h with h | h
      · right
        refine ⟨0, Fin.ext ?_⟩
        change x.val = y.val
        obtain ⟨hle, hdiff⟩ := Bool.and_eq_true_iff.mp h
        have hle' := of_decide_eq_true hle
        have hzero : y.val - x.val = 0 := by
          by_contra hn
          cases hd : y.val - x.val with
          | zero => exact hn hd
          | succ n =>
            rw [hd] at hdiff
            change (Nat.bit true 0).testBit n.succ = true at hdiff
            rw [Nat.testBit_bit_succ, Nat.zero_testBit] at hdiff
            contradiction
        omega
      · exact Or.inl h
    rw [step]
    split
    · exact mark
    · intro h
      rcases ih (x := p x) (b := (1 <<< x.val) ||| b) h with h | ⟨k, h⟩
      · exact mark h
      · exact Or.inr ⟨k+1, by simpa only [Function.iterate_succ_apply] using h⟩

private theorem test_step_mono (p : P) (a x y : Fin 23) (n b : Nat)
    (hb : b.testBit y.val = true) : (step p a n x b).2.testBit y.val = true := by
  induction n generalizing x b with
  | zero => exact hb
  | succ n ih =>
    have mark : (((1 <<< x.val) ||| b).testBit y.val) = true := by simp [Nat.testBit_or, hb]
    rw [step]
    split
    · exact mark
    · exact ih _ _ mark

private theorem test_step_self (p : P) (a x : Fin 23) (n b : Nat) :
    (step p a (n+1) x b).2.testBit x.val = true := by
  have mark : (((1 <<< x.val) ||| b).testBit x.val) = true := by
    simp [Nat.testBit_or, Nat.testBit_shiftLeft]
  rw [step]
  split
  · exact mark
  · exact test_step_mono _ _ _ _ _ _ mark

private def update (p : P) (s : Nat × Nat) (x : Fin 23) : Nat × Nat :=
  if s.1.testBit x.val then s else
    let (d, bits) := step p x 23 x s.1
    (bits, Nat.lcm s.2 d)

private def periodLcm (p : P) : Nat := ((List.finRange 23).foldl (update p) (0, 1)).2

private theorem step_period (p : P) (a : Fin 23) (b : Nat) :
    (step p a 23 a b).1 = minimalPeriod p a := by
  have hp := minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts a)
  have hc : minimalPeriod p a ≤ 23 := by simpa using minimalPeriod_le_card (f := p) (x := a)
  simpa using step_fst p a (n := 23) (k := 0) hp (by simpa using hc) b

private theorem period_dvd_iff_pow (p : P) (n : Nat) :
    (∀ x, minimalPeriod p x ∣ n) ↔ p ^ n = 1 := by
  simp only [← isPeriodicPt_iff_minimalPeriod_dvd, IsPeriodicPt, IsFixedPt]
  rw [Equiv.ext_iff]
  simp only [Equiv.Perm.coe_pow, Perm.one_apply]

private theorem periodLcm_eq (p : P) : periodLcm p = orderOf p := by
  have hp (x) : minimalPeriod p x ∣ orderOf p :=
    (period_dvd_iff_pow _ _).mpr (pow_orderOf_eq_one p) x
  have aux (xs : List (Fin 23)) (s : Nat × Nat)
      (ha : s.2 ∣ orderOf p)
      (hb : ∀ x : Fin 23, s.1.testBit x.val = true → minimalPeriod p x ∣ s.2) :
      let t := xs.foldl (update p) s
      t.2 ∣ orderOf p ∧
        (∀ x ∈ xs, t.1.testBit x.val = true) ∧
        (∀ x : Fin 23, s.1.testBit x.val = true → t.1.testBit x.val = true) ∧
        ∀ x : Fin 23, t.1.testBit x.val = true → minimalPeriod p x ∣ t.2 := by
    induction xs generalizing s with
    | nil => exact ⟨ha, by simp, fun _ h => h, hb⟩
    | cons a xs ih =>
      have hnew : (update p s a).1.testBit a.val = true := by
        unfold update
        split
        · simpa
        · exact test_step_self _ _ _ _ _
      have hmono (x : Fin 23) (h : s.1.testBit x.val = true) :
          (update p s a).1.testBit x.val = true := by
        unfold update
        split
        · exact h
        · exact test_step_mono _ _ _ _ _ _ h
      have hra : (update p s a).2 ∣ orderOf p := by
        unfold update
        split
        · exact ha
        · change Nat.lcm s.2 (step p a 23 a s.1).1 ∣ orderOf p
          rw [step_period]
          exact Nat.lcm_dvd ha (hp a)
      have hrb (x : Fin 23) (h : (update p s a).1.testBit x.val = true) :
          minimalPeriod p x ∣ (update p s a).2 := by
        unfold update at h ⊢
        by_cases hmarked : s.1.testBit a.val = true
        · simp only [hmarked] at h ⊢
          exact hb x h
        · simp only [hmarked] at h ⊢
          change (step p a 23 a s.1).2.testBit x.val = true at h
          change minimalPeriod p x ∣ Nat.lcm s.2 (step p a 23 a s.1).1
          rw [step_period]
          rcases step_bits _ _ _ _ _ _ h with h | ⟨k, rfl⟩
          · exact (hb x h).trans (Nat.dvd_lcm_left ..)
          · rw [minimalPeriod_apply_iterate (p.injective.mem_periodicPts a)]
            exact Nat.dvd_lcm_right ..
      obtain ⟨hd, hx, hh, hv⟩ := ih _ hra hrb
      refine ⟨hd, ?_, fun x h => hh x (hmono x h), hv⟩
      intro x h
      rcases List.mem_cons.mp h with rfl | h
      · exact hh _ hnew
      · exact hx x h
  obtain ⟨h1, h2, _, h3⟩ := aux (List.finRange 23) (0, 1) (one_dvd _) (by simp)
  refine h1.antisymm (orderOf_dvd_iff_pow_eq_one.mpr ((period_dvd_iff_pow _ _).mp ?_))
  exact fun x => h3 x (h2 x (List.mem_finRange x))

private def histogram (grade : P → Nat) (ps : List P) : List Nat :=
  ps.foldl (fun counts p => counts.modify (min 15 (grade p)) (· + 1))
    (List.replicate 16 0)

private theorem histogram_get (grade : P → Nat) (ps : List P) (i : Fin 16) :
    (histogram grade ps)[i.val]?.getD 0 = ps.countP (fun p => min 15 (grade p) == i.val) := by
  have h (xs : List P) (ys : List Nat) (hy : ys.length = 16) :
      (xs.foldl (fun counts p => counts.modify (min 15 (grade p)) (· + 1))
        ys)[i.val]?.getD 0 =
        ys[i.val]?.getD 0 + xs.countP (fun p => min 15 (grade p) == i.val) := by
    induction xs generalizing ys with
    | nil => simp
    | cons p xs ih =>
      rw [List.foldl_cons, ih _ (by simpa using hy), List.countP_cons]
      by_cases he : min 15 (grade p) = i.val <;>
        simp [he, List.getElem?_eq_getElem (show i.val < ys.length by omega)]; omega
  rw [histogram, h _ _ (List.length_replicate ..), List.getElem?_replicate, ite_eq_left i.isLt]
  exact Nat.zero_add _

/- Fixing the first two representatives divides each enumeration into
batches. Two batches are conjugate when an element of the common tail
subgroup carries the two prescribed images to each other. -/
private structure BatchFamily where
  first : Level
  second : Level
  tail : List Level

private abbrev BatchFamily.levels (B : BatchFamily) := B.first :: B.second :: B.tail

private def BatchFamily.prefixes (B : BatchFamily) : List P :=
  (B.first.reps.map Prod.fst).flatMap fun r => (B.second.reps.map Prod.fst).map (r * ·)

private def BatchFamily.batch (B : BatchFamily) (r : P) : List P :=
  (enumerated (coords B.tail)).map (r * ·)

private def lookup {A : Type*} [Inhabited A] (xs : List A) (i : Nat) : A :=
  xs[i]?.getD default

private def profilePrefix (B : BatchFamily) (profiles : List (Nat × List Nat)) (i : Nat) : P :=
  (B.prefixes[(lookup profiles i).1]?).getD 1

private def profilesOK (B : BatchFamily) (profiles : List (Nat × List Nat)) : Bool :=
  profiles.all fun (i, h) => decide (i < B.prefixes.length) &&
    histogram periodLcm (B.batch (B.prefixes[i]?.getD 1)) == h

private def witnessOK (B : BatchFamily) (profiles : List (Nat × List Nat))
    (q : P) (cert : Nat × P) : Bool :=
  let (i, k) := cert
  let p := profilePrefix B profiles i
  decide (i < profiles.length) && sift (coords B.tail) k &&
  k (p B.first.point) == q B.first.point && k (p B.second.point) == q B.second.point

private theorem enumerated_batches (B : BatchFamily) :
    enumerated (coords B.levels) = B.prefixes.flatMap B.batch := by
  simp [BatchFamily.prefixes, BatchFamily.batch, coords, enumerated,
    List.map_flatMap, List.flatMap_assoc, List.flatMap_map, List.map_map, Function.comp_def,
    mul_assoc]

private theorem prefix_mem (B : BatchFamily) (hB : validChain B.levels = true)
    {p : P} (hp : p ∈ B.prefixes) : p ∈ subgroup B.levels := by
  obtain ⟨h1, ht⟩ := Bool.and_eq_true_iff.mp hB
  obtain ⟨h2, _⟩ := Bool.and_eq_true_iff.mp ht
  obtain ⟨r, hr, hs⟩ := List.mem_flatMap.mp hp
  obtain ⟨s, hs0, rfl⟩ := List.mem_map.mp hs
  exact mul_mem (rep_mem _ _ h1 hr) (subgroup_mono_cons _ _ (rep_mem _ _ h2 hs0))

private theorem mem_batch (B : BatchFamily) (hB : validChain B.levels = true)
    {p g : P} (hp : p ∈ B.prefixes) :
    g ∈ B.batch p ↔ g ∈ subgroup B.levels ∧
      g B.first.point = p B.first.point ∧ g B.second.point = p B.second.point := by
  have hB' := (Bool.and_eq_true_iff.mp hB).2
  have ht := (Bool.and_eq_true_iff.mp hB').2
  have stab (k : P) : k ∈ subgroup B.tail ↔
      k ∈ subgroup B.levels ∧ k B.first.point = B.first.point ∧
        k B.second.point = B.second.point := by
    rw [tail_eq_stabilizer hB', tail_eq_stabilizer hB]
    exact and_assoc
  have hmem : g ∈ B.batch p ↔ p⁻¹ * g ∈ subgroup B.tail := by
    rw [BatchFamily.batch, List.mem_map]
    refine ⟨?_, fun h => ⟨p⁻¹ * g, ((validChain_spec _ ht).1 _).mpr h, by simp⟩⟩
    rintro ⟨k, hk, rfl⟩
    simpa using ((validChain_spec _ ht).1 _).mp hk
  rw [hmem, stab, (subgroup B.levels).mul_mem_cancel_left (inv_mem (prefix_mem B hB hp))]
  constructor
  · rintro ⟨hg, h1, h2⟩
    exact ⟨hg, by simpa [Perm.mul_apply] using congrArg p h1,
      by simpa [Perm.mul_apply] using congrArg p h2⟩
  · rintro ⟨hg, h1, h2⟩
    exact ⟨hg, by simp [Perm.mul_apply, h1], by simp [Perm.mul_apply, h2]⟩

private theorem batch_perm (B : BatchFamily) (hB : validChain B.levels = true)
    {p q k : P} (hp : p ∈ B.prefixes) (hq : q ∈ B.prefixes) (hk : k ∈ subgroup B.tail)
    (h1 : k (p B.first.point) = q B.first.point)
    (h2 : k (p B.second.point) = q B.second.point) :
    ((B.batch p).map (fun g => k * g * k⁻¹)).Perm (B.batch q) := by
  have ht := (Bool.and_eq_true_iff.mp hB).2
  have htail := (Bool.and_eq_true_iff.mp ht).2
  have nodup (r : P) : (B.batch r).Nodup :=
    (validChain_spec _ htail).2.map (mul_right_injective r)
  have hkg := ((subgroup_mono_cons B.second B.tail).trans
    (subgroup_mono_cons B.first (B.second :: B.tail))) hk
  have k1 : k B.first.point = B.first.point :=
    tail_fixed (Bool.and_eq_true_iff.mp hB).1 (subgroup_mono_cons _ _ hk)
  have k2 : k B.second.point = B.second.point := tail_fixed (Bool.and_eq_true_iff.mp ht).1 hk
  have ki1 : k⁻¹ B.first.point = B.first.point := by
    exact k.injective (by simp [k1])
  have ki2 : k⁻¹ B.second.point = B.second.point := by
    exact k.injective (by simp [k2])
  have e := (MulAut.conj k).injective
  apply (List.perm_ext_iff_of_nodup ((nodup p).map e) (nodup q)).mpr
  intro g
  rw [List.mem_map, mem_batch B hB hq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu, hu1, hu2⟩ := (mem_batch B hB hp).mp hu
    exact ⟨mul_mem (mul_mem hkg hu) (inv_mem hkg), by simp [Perm.mul_apply, ki1, hu1, h1],
      by simp [Perm.mul_apply, ki2, hu2, h2]⟩
  · rintro ⟨hg, hg1, hg2⟩
    refine ⟨k⁻¹ * g * k, (mem_batch B hB hp).mpr ⟨mul_mem (mul_mem (inv_mem hkg) hg) hkg,
      by simp [Perm.mul_apply, k1, hg1, ← h1], by simp [Perm.mul_apply, k2, hg2, ← h2]⟩, ?_⟩
    change k * (k⁻¹ * g * k) * k⁻¹ = g
    group

private theorem clipped_conj (k p : P) :
    min 15 (periodLcm (k * p * k⁻¹)) = min 15 (periodLcm p) := by
  simp only [periodLcm_eq]
  congr 1
  exact (MulAut.conj k).orderOf_eq p

private theorem batch_count_conj (B : BatchFamily) (hB : validChain B.levels = true)
    {p q k : P} (hp : p ∈ B.prefixes) (hq : q ∈ B.prefixes) (hk : k ∈ subgroup B.tail)
    (h1 : k (p B.first.point) = q B.first.point)
    (h2 : k (p B.second.point) = q B.second.point) (i : Fin 16) :
    (B.batch q).countP (fun g => min 15 (periodLcm g) == i.val) =
      (B.batch p).countP (fun g => min 15 (periodLcm g) == i.val) := by
  symm
  have h := (batch_perm B hB hp hq hk h1 h2).countP_congr
    (p := fun g => min 15 (periodLcm g) == i.val) (p' := fun g => min 15 (periodLcm g) == i.val)
    (fun _ _ => rfl)
  simpa [List.countP_map, Function.comp_def, clipped_conj] using h

private def expected (profiles : List (Nat × List Nat)) (certs : List (Nat × P))
    (i : Fin 16) : Nat :=
  (certs.map fun c => (lookup profiles c.1).2[i.val]?.getD 0).sum

private theorem total_count (B : BatchFamily) (hB : validChain B.levels = true)
    {profiles : List (Nat × List Nat)} {certs : List (Nat × P)}
    (hp : profilesOK B profiles = true) (hlen : B.prefixes.length = certs.length)
    (hc : (B.prefixes.zip certs).all (fun (q, c) => witnessOK B profiles q c) = true)
    (i : Fin 16) :
    (enumerated (coords B.levels)).countP (fun g => min 15 (periodLcm g) == i.val) =
      expected profiles certs i := by
  rw [enumerated_batches, List.countP_flatMap]
  let f := fun q => (B.batch q).countP (fun g => min 15 (periodLcm g) == i.val)
  let g := fun c : Nat × P => (lookup profiles c.1).2[i.val]?.getD 0
  change (B.prefixes.map f).sum = (certs.map g).sum
  conv_lhs => rw [← List.map_fst_zip hlen.le, List.map_map]
  conv_rhs => rw [← List.map_snd_zip hlen.ge, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pr hpr
  obtain ⟨q, c⟩ := pr
  have hq := List.mem_map_of_mem (f := Prod.fst) hpr
  rw [List.map_fst_zip hlen.le] at hq
  change q ∈ B.prefixes at hq
  have hw := List.all_eq_true.mp hc (q, c) hpr
  simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨⟨hc0, hc1⟩, hc2⟩, hc3⟩ := hw
  have hmem : lookup profiles c.1 ∈ profiles := by
    rw [lookup, List.getElem?_eq_getElem hc0, Option.getD_some]
    exact List.getElem_mem _
  have hprof := List.all_eq_true.mp hp _ hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hprof
  have hp0 : profilePrefix B profiles c.1 ∈ B.prefixes := by
    rw [profilePrefix, List.getElem?_eq_getElem hprof.1, Option.getD_some]
    exact List.getElem_mem _
  have hk := (validChain_spec _ ((Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hB).2).2)).1
    _ |>.mp (mem_enumerated_of_sift hc1)
  change (B.batch q).countP (fun g => min 15 (periodLcm g) == i.val) =
    (lookup profiles c.1).2[i.val]?.getD 0
  rw [batch_count_conj B hB hp0 hq hk hc2 hc3 i, ← histogram_get]
  have hhist : histogram periodLcm (B.batch (profilePrefix B profiles c.1)) =
      (lookup profiles c.1).2 := hprof.2
  rw [hhist]

private def pairFamily : BatchFamily := ⟨pair4, pair3, [pair2, pair1, pair0]⟩
private def blockFamily : BatchFamily := ⟨block5, block4, [block3, block2, block1, block0]⟩
/- A profile gives a batch index and a histogram of its orders. Each
transport entry selects a profile and gives the conjugating permutation
for the corresponding batch. Bucket 15 records every order at least 15. -/
private def pairProfiles : List (Nat × List Nat) := [
  (0, [0, 1, 75, 320, 180, 384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (1, [0, 0, 12, 96, 180, 384, 0, 288, 0, 0, 0, 0, 0, 0, 0, 0]),
  (21, [0, 0, 40, 0, 360, 0, 320, 0, 240, 0, 0, 0, 0, 0, 0, 0]),
  (22, [0, 0, 4, 0, 108, 0, 320, 0, 240, 0, 0, 0, 0, 0, 288, 0])]

private def pairTransport : List (Nat × P) := [
  (0, 1),
  (1, 1),
  (1, packed 22321094333208014997106376689453088
    18439536166448984518321637084891168 (by decide +kernel)),
  (1, packed 17740265617453417743212560060155936
    17740265617453417743212560060155936 (by decide +kernel)),
  (1, packed 22255756089917247885745278738958368
    24892275101534057238314048894273568 (by decide +kernel)),
  (1, packed 22978883985993180636728849964697632
    27962058153478692044096880588097568 (by decide +kernel)),
  (1, packed 22884230703974010370441351171147808
    13494475753191259157577018101991456 (by decide +kernel)),
  (1, packed 22581116287950079340610394915112992
    11202634034112171575021556560562208 (by decide +kernel)),
  (1, packed 22538052261268209158440351968856096
    16004889401733664673175916058773536 (by decide +kernel)),
  (1, packed 22489769660198694658371798831564832
    19926919891566173398240611930736672 (by decide +kernel)),
  (1, packed 22453050268928471392462583671162912
    12420898256453154516473586541660192 (by decide +kernel)),
  (1, packed 22852781804489810799839963914864672
    7272095176193669210881269563918368 (by decide +kernel)),
  (1, packed 20146944983099834036853653608269856
    8620434523583009193481064382892064 (by decide +kernel)),
  (1, packed 22806646448576353192152333205080096
    23748787413519650650161438583687200 (by decide +kernel)),
  (1, packed 18644930765349261608514054662916128
    18644930765349261608514054662916128 (by decide +kernel)),
  (1, packed 9513264885904104040016395193845792
    19658114106476692182561598510106656 (by decide +kernel)),
  (1, packed 18359910197598529884369643395156000
    8407854939806122548181496560617504 (by decide +kernel)),
  (1, packed 18561539526256435391920881438132256
    15788731992045256177750067984730144 (by decide +kernel)),
  (1, packed 7398547991451487267986502981388320
    27588612146144558575139404079695904 (by decide +kernel)),
  (1, packed 22728237725033436153095829507967008
    9227794096546495382497070466730016 (by decide +kernel)),
  (1, packed 22374289970633997496708239128725536
    4192383850574162936088311257106464 (by decide +kernel)),
  (2, 1),
  (3, 1),
  (3, packed 8339264913346975636621282356856864
    8339264913346975636621282356856864 (by decide +kernel)),
  (3, packed 6026793697417781017620123956119584
    21526475516956751246909948494448672 (by decide +kernel)),
  (3, packed 6789787198876767537668992403638304
    18467382931332763568158902016444448 (by decide +kernel)),
  (3, packed 6840686461469905537198061597624352
    6840686461469905537198061597624352 (by decide +kernel)),
  (3, packed 26133266016585805119667280265971744
    9480099582244954774698510831945760 (by decide +kernel)),
  (3, packed 23655125450927563503526748921890848
    13238855680449285518178617634424864 (by decide +kernel)),
  (3, packed 24034283315618573087829625399248928
    25121772452457763312800911875737632 (by decide +kernel)),
  (3, packed 13535599455901124075072634242566176
    25491604893941797862406101447837728 (by decide +kernel)),
  (3, packed 20371673964484842669988457203468320
    27888680184962752334443789918767136 (by decide +kernel)),
  (3, packed 9746232050451908501780066813970464
    9746232050451908501780066813970464 (by decide +kernel)),
  (3, packed 5646444389193062444091493351262240
    17296427879406494959971276756715552 (by decide +kernel)),
  (3, packed 15070126411289325635615674521978912
    11982670887287376714964203415373856 (by decide +kernel)),
  (3, packed 8199971786665308201317631209343008
    12355958966072381278280338871781408 (by decide +kernel)),
  (3, packed 5982885655848120470344932700293152
    5982885655848120470344932700293152 (by decide +kernel)),
  (3, packed 12355958966072381278280338871781408
    8199971786665308201317631209343008 (by decide +kernel)),
  (3, packed 22321094333208014997106376689453088
    18439536166448984518321637084891168 (by decide +kernel)),
  (3, packed 16445493887627351993936736990365728
    20346086079600431876274273725286432 (by decide +kernel)),
  (3, packed 7125874637030414451825648838248480
    22887802251828804903568732145059872 (by decide +kernel)),
  (3, packed 8132473978768993794263732077037600
    14454276356560267748269578306816032 (by decide +kernel))]

private def blockProfiles : List (Nat × List Nat) := [
  (0, [0, 1, 75, 320, 180, 384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  (1, [0, 0, 24, 96, 216, 384, 96, 0, 144, 0, 0, 0, 0, 0, 0, 0]),
  (6, [0, 0, 0, 48, 96, 192, 144, 192, 96, 0, 0, 0, 0, 0, 192, 0]),
  (11, [0, 0, 40, 0, 360, 0, 320, 0, 240, 0, 0, 0, 0, 0, 0, 0]),
  (12, [0, 0, 4, 24, 132, 96, 200, 192, 120, 0, 0, 0, 0, 0, 192, 0]),
  (13, [0, 0, 0, 48, 96, 192, 144, 192, 96, 0, 0, 0, 0, 0, 192, 0]),
  (15, [0, 0, 24, 96, 216, 384, 96, 0, 144, 0, 0, 0, 0, 0, 0, 0])]

private def blockTransport : List (Nat × P) := [
  (0, 1),
  (1, 1),
  (1, packed 26353248423483647160200251537705171
    20310301072505503629449424571633259 (by decide +kernel)),
  (1, packed 19864810400891648332586247690684430
    26582022912533028410577879576283681 (by decide +kernel)),
  (1, packed 28941971676221544621322035922487339
    28941971676221544621322035922487339 (by decide +kernel)),
  (1, packed 27650720571035592946062003265912839
    12600866746998031488705306862759137 (by decide +kernel)),
  (2, 1),
  (2, packed 29193003682847635256678133884038289
    29388202612292163361307446492673138 (by decide +kernel)),
  (2, packed 26880970971801220150071450378191879
    28099238462251807437080639392265441 (by decide +kernel)),
  (2, packed 26353248423483647160200251537705171
    20310301072505503629449424571633259 (by decide +kernel)),
  (2, packed 28098846430569716296643601541548036
    26881246753176415118077987687713921 (by decide +kernel)),
  (3, 1),
  (4, 1),
  (5, 1),
  (4, packed 28171096374833703844607207506784387
    28171637114076126402064149994556782 (by decide +kernel)),
  (6, 1),
  (4, packed 20309271959176042218424450104733838
    20309672887323423026477658292162957 (by decide +kernel)),
  (4, packed 26598123529227600069181671716562950
    26598367936543096806410601127855681 (by decide +kernel)),
  (4, packed 28177638918961427373498233460705488
    28178053458432738311145373088291980 (by decide +kernel)),
  (6, packed 26353248423483647160200251537705171
    20310301072505503629449424571633259 (by decide +kernel)),
  (4, packed 26353248423483647160200251537705171
    20310301072505503629449424571633259 (by decide +kernel)),
  (5, packed 26353248423483647160200251537705171
    20310301072505503629449424571633259 (by decide +kernel)),
  (4, packed 12522408479440324493367505255237956
    26597029560928756685795640872208977 (by decide +kernel)),
  (4, packed 29421541843840814030507338912663873
    29429001833290322348621359483127818 (by decide +kernel)),
  (4, packed 28163798660086772480106624697615570
    28163512317555983758737170533726573 (by decide +kernel)),
  (6, packed 19864810400891648332586247690684430
    26582022912533028410577879576283681 (by decide +kernel)),
  (5, packed 19864810400891648332586247690684430
    26582022912533028410577879576283681 (by decide +kernel)),
  (4, packed 19864810400891648332586247690684430
    26582022912533028410577879576283681 (by decide +kernel)),
  (4, packed 12318219543660249746089157690049735
    20294118139272689915835287115150734 (by decide +kernel)),
  (4, packed 29429001833290322348621359483127818
    29421541843840814030507338912663873 (by decide +kernel)),
  (6, packed 28941971676221544621322035922487339
    28941971676221544621322035922487339 (by decide +kernel)),
  (4, packed 12600731697881887831643431075692876
    27650130294866499836449523551670737 (by decide +kernel)),
  (4, packed 28941971676221544621322035922487339
    28941971676221544621322035922487339 (by decide +kernel)),
  (4, packed 20310866406116390616869811473696802
    26353428884685122990654532739399724 (by decide +kernel)),
  (4, packed 26581460066915635813718202067829062
    19864379964079114959911842184547754 (by decide +kernel)),
  (5, packed 28941971676221544621322035922487339
    28941971676221544621322035922487339 (by decide +kernel)),
  (6, packed 27650720571035592946062003265912839
    12600866746998031488705306862759137 (by decide +kernel)),
  (4, packed 12554318938368212629487336787395630
    12554318938368212629487336787395630 (by decide +kernel)),
  (4, packed 26596745113973526859941047038951434
    12522531294220054059476188709204065 (by decide +kernel)),
  (4, packed 27650720571035592946062003265912839
    12600866746998031488705306862759137 (by decide +kernel)),
  (5, packed 27650720571035592946062003265912839
    12600866746998031488705306862759137 (by decide +kernel)),
  (4, packed 20294232102297641695946913139246130
    12317919433891932046648482204985389 (by decide +kernel))]

private theorem equation_card (K : Subgroup P) (ps : List P) (hn : ps.Nodup)
    (hK : ∀ g, g ∈ ps ↔ g ∈ K) (n : Nat) :
    Nat.card {g : K // g ^ n = 1} = (ps.map orderOf).countP (fun d => decide (d ∣ n)) := by
  let p : P → Bool := fun g => decide (orderOf g ∣ n)
  let xs := ps.filter p
  let s : Finset P := ⟨(xs : Multiset P), hn.filter _⟩
  have e (g : P) : g ∈ s ↔ g ∈ K ∧ g ^ n = 1 := by
    change g ∈ xs ↔ _
    simp [xs, p, hK, orderOf_dvd_iff_pow_eq_one]
  let equiv : {g : K // g ^ n = 1} ≃ (s : Type) :=
    { toFun g := ⟨g.1.1, (e _).2 ⟨g.1.2, congrArg Subtype.val g.2⟩⟩
      invFun g := ⟨⟨g.1,(e _).1 g.2 |>.1⟩, Subtype.ext ((e _).1 g.2 |>.2)⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_coe, List.countP_map,
    List.countP_eq_length_filter]
  rfl

private abbrev pairList := enumerated (coords pairChain)
private abbrev blockList := enumerated (coords blockChain)

private theorem order_perm_of_counts {a b : List P}
    (h : ∀ i : Fin 16, a.countP (fun g => min 15 (periodLcm g) == i.val) =
      b.countP (fun g => min 15 (periodLcm g) == i.val))
    (ha : a.countP (fun g => min 15 (periodLcm g) == 15) = 0) :
    (a.map orderOf).Perm (b.map orderOf) := by
  have hclip : (a.map (fun g => min 15 (periodLcm g))).Perm
      (b.map (fun g => min 15 (periodLcm g))) := by
    rw [List.perm_iff_count]
    intro d
    simp only [List.count_eq_countP, List.countP_map]
    by_cases hd : d < 16
    · exact h ⟨d, hd⟩
    · have he (g : P) : (min 15 (periodLcm g) == d) = false :=
        beq_eq_false_iff_ne.mpr fun he => by have := min_le_left 15 (periodLcm g); omega
      simp only [Function.comp_def, he, List.countP_false]
      rfl
  have hb : b.countP (fun g => min 15 (periodLcm g) == 15) = 0 := (h 15).symm.trans ha
  have map_eq {l : List P} (hl : l.countP (fun g => min 15 (periodLcm g) == 15) = 0) :
      l.map (fun g => min 15 (periodLcm g)) = l.map orderOf := by
    apply List.map_congr_left
    intro g hg
    rw [List.countP_eq_zero] at hl
    have hle : periodLcm g ≤ 15 := by
      by_contra h
      have he : min 15 (periodLcm g) = 15 := min_eq_left (by omega)
      exact hl g hg (by simp [he])
    rw [min_eq_right hle, periodLcm_eq]
  rwa [map_eq ha, map_eq hb] at hclip

private theorem orders_coincide
    (hpair : profilesOK pairFamily pairProfiles = true)
    (hblock : profilesOK blockFamily blockProfiles = true) :
    (pairList.map orderOf).Perm (blockList.map orderOf) := by
  have ha := total_count pairFamily pair_valid hpair
    (certs := pairTransport) (by decide +kernel) (by decide +kernel)
  have hb := total_count blockFamily block_valid hblock
    (certs := blockTransport) (by decide +kernel) (by decide +kernel)
  have h : ∀ i, expected pairProfiles pairTransport i = expected blockProfiles blockTransport i :=
    by decide +kernel
  have h0 : expected pairProfiles pairTransport 15 = 0 := by decide +kernel
  exact order_perm_of_counts (fun i => (ha i).trans ((h i).trans (hb i).symm))
    ((ha 15).trans h0)
universe u v

private theorem socle_simple : IsSimpleGroup PairSocle := by
  let := pairSimple_simple
  exact pairSocleEquiv.symm.isSimpleGroup

private theorem socle_noncomm : ¬ IsMulCommutative PairSocle := by
  intro h
  apply pairSimple_noncomm
  exact IsMulCommutative.of_comm fun a b => pairSocleEquiv.injective (by
    rw [map_mul, map_mul, mul_comm'])

/- Conjugation embeds the pair stabilizer in the automorphism group of its
simple normal subgroup. The lifts let the two finite witnesses inhabit
the independently quantified universes in the conjecture. -/
private theorem pair_almost_simple : IsAlmostSimple (ULift.{u} PairGroup) := by
  let := socle_simple
  let e : PairSocle ≃* ULift.{u} PairSocle := MulEquiv.ulift.symm
  let f := (MulAut.congr e).toMonoidHom.comp
    ((conjAction PairSocle).comp (MulEquiv.ulift : ULift.{u} PairGroup ≃* PairGroup).toMonoidHom)
  have hf : Function.Injective f := (MulAut.congr e).injective.comp
    ((conjAction_injective PairSocle pair_centralizer).comp MulEquiv.ulift.injective)
  have hs : IsSimpleGroup (ULift.{u} PairSocle) := e.symm.isSimpleGroup
  have hnc : ¬ IsMulCommutative (ULift.{u} PairSocle) := by
    intro h
    exact socle_noncomm (IsMulCommutative.of_comm fun a b => e.injective (by
      rw [map_mul, map_mul, mul_comm']))
  refine ⟨ULift.{u} PairSocle, inferInstance, inferInstance, hs, hnc,
    f.range, ?_, ⟨MonoidHom.ofInjective hf⟩⟩
  rintro _ ⟨s, rfl⟩
  refine ⟨⟨s.down.val⟩, ?_⟩
  exact MulEquiv.ext fun _ => rfl

private theorem not_isomorphic : ¬ Nonempty (PairGroup ≃* BlockGroup) := by
  rintro ⟨e⟩
  let N := BlockKernel.comap e.toMonoidHom
  have : N.Normal := inferInstanceAs (BlockKernel.comap e.toMonoidHom).Normal
  have : IsMulCommutative N := BlockKernel.comap_injective_isMulCommutative e.injective
  let := socle_simple
  have hN := no_abelian_normal PairSocle socle_noncomm pair_centralizer N
  apply blockKernel_ne_bot
  apply Subgroup.comap_injective (f := e.toMonoidHom) e.surjective
  change N = e.toMonoidHom.ker
  exact hN.trans ((e.toMonoidHom.ker_eq_bot_iff).mpr e.injective).symm

private theorem ulift_equation_card {G : Type*} [Group G] (n : Nat) :
    Nat.card {g : ULift.{u} G // g ^ n = 1} = Nat.card {g : G // g ^ n = 1} :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.down, congrArg ULift.down g.2⟩
      invFun := fun g => ⟨⟨g.1⟩, congrArg ULift.up g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem conclude
    (hpair : profilesOK pairFamily pairProfiles = true)
    (hblock : profilesOK blockFamily blockProfiles = true) : ¬ conjecture.{u, v} := by
  intro h
  apply not_isomorphic
  obtain ⟨e⟩ := h (ULift.{u} PairGroup) (ULift.{v} BlockGroup) pair_almost_simple (by
    intro n _
    rw [ulift_equation_card, ulift_equation_card,
      equation_card _ pairList (validChain_spec _ pair_valid).2 (validChain_spec _ pair_valid).1,
      equation_card _ blockList (validChain_spec _ block_valid).2 (validChain_spec _ block_valid).1]
    exact (orders_coincide hpair hblock).countP_congr (fun _ _ => rfl))
  exact ⟨MulEquiv.ulift.symm.trans (e.trans MulEquiv.ulift)⟩

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
-- Kernel reduction counts orders over every permutation in the selected batches.
private theorem pair_profiles_ok : profilesOK pairFamily pairProfiles = true := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
-- Kernel reduction counts orders over every permutation in the selected batches.
private theorem block_profiles_ok : profilesOK blockFamily blockProfiles = true := by decide +kernel

/--
**Power-equation type does not characterize almost simple groups.** There exist finite
groups $G$ and $H$ such that $G$ is almost simple, $G$ and $H$ have the same power-equation type,
and $G$ is not isomorphic to $H$. That is, the conjecture of Kourovka Problem 21.134(b) is false.

Kourovka Notebook v46 records that J. G. Thompson had already given a negative answer to part (b).

Source: Yu Li and Wujie Shi, A Note on Thompson Problem, arXiv:2303.09460v1 (2023);
published in Ricerche di Matematica 74(1) (2025), 559-563, https://arxiv.org/abs/2303.09460v1;
The Kourovka Notebook: Unsolved Problems in Group Theory, 21st edition, Problem 21.134,
arXiv:1401.0300v46, https://arxiv.org/abs/1401.0300v46. Moved from
`OpenConjectures/GroupTheory/Kourovka21Problem134b`.
-/
public theorem conjecture_refuted : ¬ conjecture :=
  conclude pair_profiles_ok block_profiles_ok

end MathlibExt.GroupTheory.Kourovka21Problem134bWanted
