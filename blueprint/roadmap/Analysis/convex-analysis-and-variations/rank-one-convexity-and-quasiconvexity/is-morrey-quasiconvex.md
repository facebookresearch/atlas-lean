# Morrey quasiconvex functions on 2×2 matrices

Let

W:ℝ^\{2×2\}→ℝ.

The function W is quasiconvex in the sense of Morrey if, for every bounded open set

Ω⊂ℝ²,

every

A∈ℝ^\{2×2\},

and every smooth compactly supported function

φ∈ C_c^∞(Ω;ℝ²),

one has

W(A)≤1/(|Ω|) ∫_Ω W(A+Dφ(x)) dx.

Equivalently,

|Ω|W(A) ≤ ∫_Ω W(A+Dφ(x)) dx.

The Lean definition uses this latter, unnormalized form.
