/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Height.NumberField

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Matveev's lower bound for linear forms in logarithms (real case).** Let $L$ be a number
field of degree $D = [L : \mathbb{Q}]$ with a field embedding $f : L \to \mathbb{R}$, let $s \ge 1$
be a natural number, and let $\eta_1, \dots, \eta_s \in L$ satisfy $\eta_i \ne 1$ and
$f(\eta_i) > 0$ for every $i$. Let $d_1, \dots, d_s$ be nonzero integers and let $B$ be a real
number with $B \ge 1$ and $|d_i| \le B$ for every $i$. Let $A_1, \dots, A_s$ be real numbers with
$A_j \ge \max(D\,h(\eta_j), |\log f(\eta_j)|, 0.16)$ for every $j$, where $h$ is the absolute
logarithmic Weil height. Put $\Gamma = f(\eta_1)^{d_1} \cdots f(\eta_s)^{d_s} - 1$. If
$\Gamma \ne 0$, then
$$\log|\Gamma| > -1.4 \cdot 30^{s+3} \, s^{4.5} \, D^2 (1 + \log D)(1 + \log B) \, A_1 \cdots A_s.$$

No integrality is assumed on the $\eta_i$, so the statement also covers non-integral algebraic
numbers, such as the element in the source's application whose minimal polynomial has leading
coefficient $23$. The source states the bound with $B = \max_i |d_i|$; since the right-hand side
increases with $B$, any real $B \ge 1$ bounding every $|d_i|$ may be used.

Source: archive provenance `wanted317_306_matveev_linear_forms_logarithms_d52ec211.zip`,
archive SHA-256
`871521f8571d9389873dabb8435b786b5a3b8d7ae38a8fb67f8d1171591f46c2`;
donor candidate `Matveev.lean` SHA-256
`d52ec2118c66e48da7507e08385ef54fc0d032821392b17f4613f170ce25c8f0`,
treated only as untrusted input.

Source: Salah Eddine Rihane, Chèfiath Awero Adegbindin, and Alain Togbé,
"Fermat Padovan And Perrin Numbers", Journal of Integer Sequences 23 (2020),
Article 20.6.2, Section 2.1 and its Matveev theorem.
Source URL `https://cs.uwaterloo.ca/journals/JIS/VOL23/Togbe/togbe16.tex`,
definitions-and-theorem source lines 148–178, theorem lines 172–178.
Complete-source SHA-256
`ad0552bbb1fc99375c5a5190ce2f4ba227ebd135154ad63081a4be2d9c390b24`;
definitions-and-theorem span SHA-256
`03e7497710ce05f87e0e801ff55541a4f2dc3e0c46832fc257e9ff90a9b54dfe`;
theorem span SHA-256
`d8d702c70dc0bd6a2e1b891a3453c7b187d1168572725b7943f27ae012de0561`.
The source cites Bugeaud–Mignotte–Siksek, Theorem 9.4, as a modified consequence of
E. M. Matveev, "An explicit lower bound for a homogeneous rational linear form in the
logarithms of algebraic numbers, II", Izv. Math. 64 (2000), 1217–1269. -/
public theorem_wanted matveev_lower_bound_linear_forms_logarithms
    {L : Type*} [Field L] [NumberField L]
    (s : ℕ) (hs : 0 < s)
    (f : L →ₐ[ℚ] ℝ)
    (eta : Fin s → L) (d : Fin s → ℤ) (A : Fin s → ℝ) (B : ℝ)
    (hpos : ∀ i, 0 < f (eta i))
    (hne1 : ∀ i, eta i ≠ 1)
    (hd0 : ∀ i, d i ≠ 0)
    (hB1 : 1 ≤ B)
    (hBle : ∀ i, |(d i : ℝ)| ≤ B)
    (hA : ∀ j, max (max ((Module.finrank ℚ L : ℝ) *
      NumberField.absLogHeight₁ (eta j)) |Real.log (f (eta j))|) 0.16 ≤ A j)
    (hGamma : (∏ i : Fin s, f (eta i) ^ (d i)) - 1 ≠ 0) :
    Real.log |(∏ i : Fin s, f (eta i) ^ (d i)) - 1| >
      -(1.4 * (30 : ℝ) ^ (s + 3) * Real.rpow (s : ℝ) 4.5 *
        (Module.finrank ℚ L : ℝ) ^ 2 *
        (1 + Real.log (Module.finrank ℚ L : ℝ)) *
        (1 + Real.log B) * ∏ j : Fin s, A j)

end

end MetaMathlibExt
