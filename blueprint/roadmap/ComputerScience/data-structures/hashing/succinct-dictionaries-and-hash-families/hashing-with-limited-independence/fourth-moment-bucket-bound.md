# Fourth-moment bucket bound under 5-wise independence

Let $h : U \to [r]$ be drawn from a 5-wise independent family, let $S \subseteq U$ with $|S| = n$ and maximum load $\bar\alpha = n / r < 1$, let $Q \subseteq [r]$ with $|Q| = q$, let $d > 0$ and fix $x \in U \setminus S$. Then

$$
\Pr\left[\,|\{y \in S : h(y) \in h(x) + Q\}| \ge \bar\alpha q + d\,\right] \le \frac{4 \bar\alpha q^2}{d^4}.
$$

## Proof sketch

Conditioning on $h(x) = \rho$ leaves the values of $S$ 4-wise independent and uniform. The count is a sum of $n$ indicators with mean $\bar\alpha q$; its centered fourth moment is $O(\bar\alpha q + (\bar\alpha q)^2)$ by 4-wise independence, and Markov's inequality on the fourth power gives the tail.

## Depends on

- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Proof depends on

- [Chebyshev's inequality](../../../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)

## Sources

- A. Pagh, R. Pagh and M. Ruzic, "Linear Probing with Constant Independence", SIAM Journal on Computing 39(3), 2009.
