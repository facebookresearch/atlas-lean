/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import MathlibExt.AlgebraicGeometry.AbelianSchemes

/-!
# The stable Faltings height of an abelian variety over a number field

An abelian variety over a field $K$ is an abelian scheme over $\operatorname{Spec} K$: a smooth
proper commutative group scheme with geometrically connected fibres. The stable Faltings height
$h_F(A)$ is recorded as a wanted definition in Faltings' original normalization, together with
its invariance under finite extension of the number field and Bost's lower bound.

References: G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*,
Invent. Math. 73 (1983), 349–366, <https://doi.org/10.1007/BF01388432>; É. Gaudron and
G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math. Helv. 89
(2014), 343–403, §2.3, Définition 2.1, pp. 351–352, and Corollaire 8.4, p. 400,
<https://doi.org/10.4171/CMH/322>.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FaltingsHeight

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes

universe u

/-- **Base change of an abelian variety along a field extension.** For fields $K \subseteq L$ and
an abelian variety $A$ over $K$, the abelian variety $A_L = A \times_{\operatorname{Spec} K}
\operatorname{Spec} L$ over $L$, with the group law obtained by base change. -/
abbrev fieldBaseChange {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    (A : AbelianScheme (Spec (CommRingCat.of K))) : AbelianScheme (Spec (CommRingCat.of L)) :=
  A.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- **Stable Faltings height.** Let $K$ be a number field and $A$ an abelian variety of dimension
$g$ over $K$. Choose a finite extension $L/K$ over which $A$ has semi-abelian reduction at every
finite place, a semi-abelian model $\pi : \mathcal{A} \to \operatorname{Spec} \mathcal{O}_L$ of
$A_L$ (a smooth separated commutative group scheme of finite type with generic fibre $A_L$ whose
fibres are extensions of abelian varieties by tori), and its zero section $\varepsilon$. The
invertible $\mathcal{O}_L$-module $\omega = \varepsilon^* \Omega^g_{\mathcal{A}/\mathcal{O}_L}$
satisfies $\omega \otimes_{\sigma} \mathbb{C} = H^0(A_\sigma, \Omega^g)$ for every embedding
$\sigma : L \to \mathbb{C}$; give it the metrics
$$\|s\|_\sigma^2 = \frac{1}{2^g} \int_{A_\sigma(\mathbb{C})} \left| s \wedge \bar s \right|,$$
where $\left| s \wedge \bar s \right| = i^{g^2} s \wedge \bar s$ is the associated positive volume
form. Then
$$h_F(A) = \frac{1}{[L : \mathbb{Q}]} \Bigl( \log \# \bigl( \omega / s \mathcal{O}_L \bigr)
  - \sum_{\sigma : L \to \mathbb{C}} \log \|s\|_\sigma \Bigr)$$
for any nonzero $s \in \omega$, the normalized Arakelov degree of $\omega$ with these metrics.
It does not depend on $L$, on the model or on $s$.

This is Faltings' original normalization, as described by Gaudron and Rémond, *Théorème des
périodes et degrés minimaux d'isogénies*, Comment. Math. Helv. 89 (2014), §2.3, pp. 351–352
(<https://doi.org/10.4171/CMH/322>). Their Définition 2.1 uses instead the height $h(A)$ defined
with $(2\pi)^g$ in place of $2^g$ in the metric, so that $h_F(A) = h(A) - \frac{g}{2} \log \pi$.
Reference: G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent.
Math. 73 (1983), 349–366, <https://doi.org/10.1007/BF01388432>. -/
public def_wanted faltingsHeight (K : Type u) [Field K] [NumberField K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) : ℝ

/-- **The stable Faltings height is invariant under finite extension.** Let $L/K$ be an extension
of number fields and $A$ an abelian variety over $K$. The stable Faltings height of $A_L$ equals
that of $A$: $h_F(A_L) = h_F(A)$.

This is the independence of the choice of field in the definition of the stable height, see
É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
Helv. 89 (2014), §2.3, p. 351, <https://doi.org/10.4171/CMH/322>, and G. Faltings,
*Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73 (1983), 349–366,
<https://doi.org/10.1007/BF01388432>. -/
public theorem_wanted faltingsHeight_fieldBaseChange (K : Type u) [Field K] [NumberField K]
    (L : Type u) [Field L] [NumberField L] [Algebra K L]
    (A : AbelianScheme (Spec (CommRingCat.of K))) :
    ❰faltingsHeight❱ L (fieldBaseChange L A) = ❰faltingsHeight❱ K A

/-- **Bost's lower bound for the Faltings height.** Let $A$ be an abelian variety of dimension
$g$ over a number field $K$, and let $h(A) = h_F(A) + \frac{g}{2} \log \pi$ be the height in the
normalization of Gaudron and Rémond. Then
$$h(A) \ge -\frac{1}{2} g \log (2\pi),$$
equivalently $h_F(A) \ge -\frac{g}{2} \log (2\pi^2)$ for the stable Faltings height $h_F$ in
Faltings' normalization. The dimension $g$ is the relative dimension of the smooth morphism
$A \to \operatorname{Spec} K$.

Source: É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*,
Comment. Math. Helv. 89 (2014), 343–403, Corollaire 8.4, p. 400 (a result of Bost), with the
normalization $h_F(A) = h(A) - \frac{g}{2} \log \pi$ of §2.3, p. 352,
<https://doi.org/10.4171/CMH/322>. -/
public theorem_wanted bost_lower_bound (K : Type u) [Field K] [NumberField K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ)
    [SmoothOfRelativeDimension g A.model.hom] :
    -(1 / 2 : ℝ) * g * Real.log (2 * Real.pi) ≤
      ❰faltingsHeight❱ K A + (g / 2 : ℝ) * Real.log Real.pi

end WantedExt.AlgebraicGeometry.FaltingsHeight
