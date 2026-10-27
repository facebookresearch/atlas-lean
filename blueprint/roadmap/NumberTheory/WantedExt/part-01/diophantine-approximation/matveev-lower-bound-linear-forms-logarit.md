---
article_id: af_637bfec33e285dc4bed4bbef
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.matveev_lower_bound_linear_forms_logarithms
---

# Matveev Linear Forms Wanted

Matveev lower bound for a linear form in logarithms (wishlist).

Archive provenance: `wanted317_306_matveev_linear_forms_logarithms_d52ec211.zip`,
archive SHA-256
`871521f8571d9389873dabb8435b786b5a3b8d7ae38a8fb67f8d1171591f46c2`;
donor candidate `Matveev.lean` SHA-256
`d52ec2118c66e48da7507e08385ef54fc0d032821392b17f4613f170ce25c8f0`,
treated only as untrusted input.

Scope: wishlist statement only; no proof is claimed here. The height is Mathlib's
canonical `NumberField.absLogHeight₁`, not a local minpoly-root formula. In particular,
no `IsIntegral ℤ` restriction and no hand-expanded leading-coefficient-free height is
retained, so the statement also covers the paper's own non-integral application element
(minimal-polynomial leading coefficient 23).

Notation adaptation: the live source writes `Gamma = ∏ ηᵢ ^ dᵢ - 1`, degree `l`,
and exact maximum `D = max |dᵢ|`; the archive quote renders these as `Lambda`, `s`,
`B`. This declaration uses `s`, `B`, and `Gamma = (∏ i, f (η i) ^ d i) - 1`, with
`B` any real upper bound with `1 ≤ B` and `|(d i : ℝ)| ≤ B`. Since the right-hand side
is monotone in the exponent bound, this `B ≥ max |dᵢ|` form is the standard
application-ready form of the source's exact-maximum `D` statement.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.DiophantineApproximation.MatveevLinearFormsWanted](../../../../../sources/v2/WantedExt.md)
- Salah Eddine Rihane, Chèfiath Awero Adegbindin, and Alain Togbé, "Fermat Padovan And Perrin Numbers", Journal of Integer Sequences 23 (2020), Article 20.6.2, Section 2.1 and its Matveev theorem. Source URL `https://cs.uwaterloo.ca/journals/JIS/VOL23/Togbe/togbe16.tex`, definitions-and-theorem source lines 148–178, theorem lines 172–178. Complete-source SHA-256 `ad0552bbb1fc99375c5a5190ce2f4ba227ebd135154ad63081a4be2d9c390b24`; definitions-and-theorem span SHA-256 `03e7497710ce05f87e0e801ff55541a4f2dc3e0c46832fc257e9ff90a9b54dfe`; theorem span SHA-256 `d8d702c70dc0bd6a2e1b891a3453c7b187d1168572725b7943f27ae012de0561`. The source cites Bugeaud–Mignotte–Siksek, Theorem 9.4, as a modified consequence of E. M. Matveev, "An explicit lower bound for a homogeneous rational linear form in the logarithms of algebraic numbers, II", Izv. Math. 64 (2000), 1217–1269.
