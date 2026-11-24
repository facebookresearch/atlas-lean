# LCA reconciliation has minimum duplication cost

**LCA reconciliation has minimum duplication cost** (Wu-Zhang 2011,
Corollary 4(a)): hypotheses are binary rooted trees with ancestor-or-self
orders (`hle_refl`, `hle_trans`), leaves exactly the childless vertices
(`hbin`), the species root above everything (`hroot`), the LCA map `M`
characterized by leaf agreement (`hMleaf`), the LCA recursion (`hMnode`),
and pointwise minimality (`hMmin`); `f` is any reconciliation. Conclusion:
`dupCost M ≤ dupCost f`.

## Sources

- Wu-Zhang (2011), Corollary 4(a) via Theorem 2.
