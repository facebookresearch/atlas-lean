# One-period fundamental theorem of asset pricing

Let $\Omega$ be a nonempty finite set of
states and $A$ a finite set of assets, and let $g(a, \omega) \in \mathbb{R}$ be the gain of
asset $a$ in state $\omega$. Call a portfolio $h \colon A \to \mathbb{R}$ an arbitrage if its
gain $\sum_{a \in A} h(a)\, g(a, \omega)$ is nonnegative in every state $\omega$ and positive
in some state. There is no arbitrage if and only if there is a function
$q \colon \Omega \to \mathbb{R}$ with $q(\omega) > 0$ for every $\omega \in \Omega$ and
$\sum_{\omega \in \Omega} q(\omega) = 1$ such that
$\sum_{\omega \in \Omega} q(\omega)\, g(a, \omega) = 0$ for every asset $a \in A$, that is, a
strictly positive probability on the states under which every asset has zero expected gain.

## Sources

- J. M. Harrison and D. M. Kreps, J. Econom. Theory 20 (1979), DOI 10.1016/0022-0531(79)90043-7. It follows from `one_period_fundamental_theorem_asset_pricing_general`; the unused `[DecidableEq Ω]` and `[DecidableEq A]` keep the source's shape.
