# Regret against a family of modification rules; internal regret

Let $X$ be a finite set of $N$ actions, $p_t \in \mathbb{R}^X$ round weights (usually distributions) and $\ell_t \in \mathbb{R}^X$ losses. For a family $F$ of maps $f : X \to X$ (memoryless modification rules), the $F$-regret over $T$ rounds is

$$
R_F^T = \sup_{f \in F} \sum_{t<T} \sum_{i \in X} p_t(i)\,\big(\ell_t(i) - \ell_t(f(i))\big).
$$

Taking $F$ the constant maps gives external regret; $F$ all maps gives swap regret; and $F^{\mathrm{in}} = \{ f_{a \to b} : a, b \in X\}$, where $f_{a\to b}$ sends $a$ to $b$ and fixes every other action, gives internal regret $\max_{a,b} \sum_{t<T} p_t(a)(\ell_t(a) - \ell_t(b))$, which is nonnegative because $f_{a \to a}$ is the identity.

## Depends on

- [External regret](../../../../GameTheory/noncooperative-games/external-and-swap-regret/external-regret.md)
- [Swap regret](../../../../GameTheory/noncooperative-games/external-and-swap-regret/swap-regret.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
- Avrim Blum and Yishay Mansour, "From External to Internal Regret", Journal of Machine Learning Research 8, 2007.
