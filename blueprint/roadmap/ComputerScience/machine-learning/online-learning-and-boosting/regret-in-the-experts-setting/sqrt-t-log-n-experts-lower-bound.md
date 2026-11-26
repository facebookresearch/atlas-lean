# General $\Omega(\sqrt{T \ln N})$ lower bound on expected external regret

Let $X$ have $N \ge 2$ actions and let $T \ge \lfloor \log_2 N \rfloor$ (for instance any $T \ge N$). There is a family of binary loss sequences indexed by uniform $w \in \{0,1\}^T$ such that every causal online algorithm $H$ has expected external regret

$$
\mathbb{E}_w\left[L_H^T(\ell^w) - L_{\min}^T(\ell^w)\right] \ge \frac{1}{4e}\sqrt{T \ln N}.
$$

## Proof sketch

Split the horizon into $k = \lfloor \log_2 N \rfloor$ blocks and arrange $2^k \le N$ actions as the leaves of a binary tree: in block $j$, each action follows the coin sequence or its complement according to its $j$-th label bit. The best leaf picks the better side in every block, so the expected regret is a sum of $k$ two-expert regrets on blocks of length about $T/k$, each at least of order $\sqrt{T/k}/(2e)$ by the two-expert bound; summing gives order $\sqrt{kT}/(2e)$, and the constant $1/(4e)$ absorbs the rounding of block lengths and the comparison $k \ge \tfrac12\log_2 N \ge \tfrac12\ln N$ for $N \ge 2$.

## Depends on

- [Causal online algorithm in the experts setting](causal-online-experts-algorithm.md)

## Proof depends on

- [Every experts algorithm has expected regret at least $\sqrt{T}/(2e)$ against fair coin losses](two-experts-sqrt-t-lower-bound.md)
- [Khintchine inequality](../../../../Probability/concentration-inequalities/khintchine-inequality.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
