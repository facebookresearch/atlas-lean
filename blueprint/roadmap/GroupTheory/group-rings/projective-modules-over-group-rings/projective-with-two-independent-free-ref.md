# Artamonov's freeness question has a negative answer

It is not the case that for every
commutative ring $k$, every torsion-free almost polycyclic group $G$ (no element $g \ne 1$ of $G$
has finite order) and every finitely generated projective module $P$ over the group ring $kG$
containing two elements that are linearly independent over $kG$, the module $P$ is free over $kG$.

Jayadevan's counterexample takes $k = \mathbb{F}_2 \times \mathbb{F}_2$ and the trivial group $G$,
so that $kG = k$; then $P = k^2 \oplus (\mathbb{F}_2 \times 0)$ is a finitely generated projective
$k$-module containing an independent pair, but $|P| = 32$ is not a power of $4 = |k|$, so $P$ is
not free. The Kourovka Notebook (21st issue) marks 11.5 solved, "No, not always" (AI solution
confirmed by D. Segal); the example gives nothing for field coefficients.

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.5 (V. A. Artamonov); resolution: A. Jayadevan, A coefficient-ring obstruction to freeness of projective group-ring modules, preprint, Zenodo record 22846603 (2026), main example: `k = 𝔽₂ × 𝔽₂`, `G = 1`, `P = k² ⊕ (𝔽₂ × 0)` is projective with an independent pair but has 32 elements, while finite free `k`-modules have `4ⁿ`; the Kourovka Notebook (21st issue) marks 11.5 solved (AI solution confirmed by D. Segal), https://zenodo.org/records/22846603.
