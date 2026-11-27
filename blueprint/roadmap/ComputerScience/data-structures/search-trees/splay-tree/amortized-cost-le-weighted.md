# Amortized cost of accessing a present key

For positive weights $w$ and a binary search tree $t$ containing the key $x$,

$$\mathrm{cost}(x, t) + \Phi_w(S_x(t)) - \Phi_w(t) \le 3\bigl(\log_2 W(t) - \log_2 w(x)\bigr) + 1,$$

that is, $O\bigl(1 + \log(W(t)/w(x))\bigr)$. It follows from the access lemma: in a search tree
the search for $x$ ends at the node holding $x$, whose subtree has weight $s(x) \ge w(x)$.

## Informally uses

- [Access lemma for splay trees](access-lemma-weighted.md)

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2, Lemma 1.
