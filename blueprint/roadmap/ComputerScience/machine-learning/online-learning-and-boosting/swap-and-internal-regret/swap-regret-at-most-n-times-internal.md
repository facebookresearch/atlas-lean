# Swap regret is at most N times internal regret, and the factor is tight up to one

For any finite action set $X$ with $N$ elements, any round weights $p_t \in \mathbb{R}^X$, any real losses $\ell_t \in \mathbb{R}^X$ and any horizon $T$,

$$
R_{\mathrm{swap}}^T \le N \cdot R_{\mathrm{in}}^T .
$$

Conversely, for every $N \ge 2$ there are distributions $p_t$ and binary losses over $T = N$ rounds on $N$ actions with internal regret exactly $1$ and swap regret exactly $N-1$ (uniform play against the constant loss vector $(0,1,\ldots,1)$).

## Proof sketch

Swap regret against $\delta$ decomposes as $\sum_{a} \sum_t p_t(a)(\ell_t(a) - \ell_t(\delta(a)))$, a sum of $N$ terms each at most the internal regret of the switch $a \to \delta(a)$. For tightness, uniform play gives each action weight $1$ in total; switching any lossy action to the lossless one saves $1$, and swapping all $N-1$ of them saves $N-1$.

## Depends on

- [Regret against a family of modification rules; internal regret](modification-rule-regret-and-internal-regret.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
