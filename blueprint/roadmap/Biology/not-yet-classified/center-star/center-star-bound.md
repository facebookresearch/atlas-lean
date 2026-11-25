# Center-star approximation

**Center-star approximation** (Gusfield 1993, Theorem 3.1): hypotheses are
a gap scoring with `s none none = 0` (`hgap`) and zero self-costs `s x x = 0` for every
`x : Option α` (`hdiag`), the triangle inequality
(`htria`), explicit symmetry (`hsymm`), at least two strings (`hk`), the
`pairDist` characterization (`hD_le`, `hD_att`), a center index `c : Fin k`
whose input string minimizes the center total over the inputs,
`∑ j, D (X c) (X j) ≤ ∑ j, D (X i) (X j)` for every `i : Fin k` (`hcenter`, Gusfield's selection
rule), spoke alignments `P j` that are
valid and attain the pairwise optima (`hspoke`), a star alignment `Ac`
whose induced pairwise values obey the star triangle bound (`hstar`), and an
optimal alignment `Astar` valid for `X` and minimal (`hopt`). Conclusion:
`k * V(Ac) ≤ 2 * (k - 1) * V(Astar)`.

## Sources

- Gusfield (1993), Theorem 3.1 (via Lemma 3.1).
