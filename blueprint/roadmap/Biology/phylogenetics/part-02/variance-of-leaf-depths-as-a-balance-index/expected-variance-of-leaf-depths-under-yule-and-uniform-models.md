# Expected variance of leaf depths under the Yule and uniform models

**Setting.** $V_n$ is the variance of the leaves' depths, $V(T) = S^{(2)}(T)/n - S(T)^2/n^2$, of a random bifurcating phylogenetic tree with $n$ labelled leaves, either under the **Yule** (pure-birth) model or the **uniform** model (all $(2n-3)!!$ rooted binary trees equally likely). Write $H_n = \sum_{i\le n}1/i$, $H^{(2)}_n = \sum_{i\le n}1/i^2$ and $\varrho_n = \frac{(2n-2)!!}{(2n-3)!!}$.

**Theorem.**

1. *(Yule.)* $E_Y\big(S^{(2)}_n\big) = 2n\big(2H_n^2 - 3H_n - 2H^{(2)}_n + 3\big)$ and

    $$E_Y(V_n) = \frac{2(n+1)}{n}H_n + \frac1n - 5 \sim 2\ln n.$$

2. *(Uniform.)* $E_U\big(S^{(2)}_n\big) = 4n^2 - n - 3n\varrho_n$, $E_U\big(S_n^2\big) = \frac{10n^3 - n}{3} - \frac{5n^2 + n}{2}\varrho_n$, and

    $$E_U(V_n) = \frac{(2n-1)(n-1)}{3n} - \frac{n-1}{2n}\varrho_n \sim \frac23 n.$$

3. *(Variance of the Sackin index, uniform.)* With $E_U(S_n) = n(\varrho_n - 1)$,

    $$\sigma^2_U(S_n) = \frac{n(10n^2 - 3n - 1)}{3} - \frac{n(n+1)}{2}\varrho_n - n^2\varrho_n^2.$$

Under the Yule model the mean depth $E_Y(S_n)/n = 2H_n - 2$ and the depth variance both grow like $2\ln n$; under the uniform model the mean depth grows like $\sqrt{\pi n}$ (since $\varrho_n \sim \sqrt{\pi n}$) while the variance grows linearly.

## Depends on

- [Extremal trees for the variance of leaf depths](extremal-trees-for-the-variance-of-leaf-depths.md)
- [Schröder's count of rooted binary phylogenetic trees](../../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/nat-card-rooted-binary-tree.md)

## Expansion

Linearity gives $E(V_n) = E(S^{(2)}_n)/n - E(S_n^2)/n^2$, so it suffices to know the first moment of $S^{(2)}$ and the second moment of $S$. Under both models a random tree splits at the root into independent random subtrees of sizes $k$ and $n-k$ (with probability $1/(n-1)$ under Yule and proportional to the number of tree pairs under the uniform model), and every leaf depth increases by one; this gives linear recurrences of the form $X_n = 2\sum_k C_{k,n-k}X_k + (\text{explicit term})$, solved in closed form. Small cases check the formulas: for $n = 3$ every tree has depths $1,2,2$, $V = 2/9$, and both expressions give $2/9$; for $n = 2$ the Yule formula gives $0$.

## Sources

- T. M. Coronado, A. Mir, F. Rosselló, L. Rotger, "On Sackin's original proposal: the variance of the leaves' depths as a phylogenetic balance index", BMC Bioinformatics 21 (2020) 154, Theorems 4–6, Propositions 1–4, Eqs (4)–(8) and Remarks 1–2, <https://doi.org/10.1186/s12859-020-3405-1>, PMCID PMC7181513.
