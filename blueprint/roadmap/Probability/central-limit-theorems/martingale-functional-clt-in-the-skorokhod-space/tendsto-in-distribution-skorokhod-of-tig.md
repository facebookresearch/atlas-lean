# Transfer of functional limit theorems from `C([0,T])` to `D([0,T])` (continuous limit)

Let $T > 0$, let $X_n$ be $D([0,T])$-valued and $Y_n$ $C([0,T])$-valued processes on a probability space, almost everywhere measurable, and let $Z$ be an almost everywhere measurable $C([0,T])$-valued process on a second probability space. Assume
* *tightness*: the laws of $Y_n$ on $C([0,T])$ form a tight family;
* *finite-dimensional convergence*: for every finite set of times $I$, $(Y_n(t))_{t \in I}$ converges in distribution to $(Z(t))_{t \in I}$;
* *jump control*: for each $\varepsilon > 0$ there are measurable sets $A_n$ with $P(A_n) \to 0$ and $\sup_t \lvert X_n(t) - Y_n(t)\rvert \le \varepsilon$ outside $A_n$.

Then $X_n \to Z$ in distribution in the Skorokhod J1 topology on $D([0,T])$.

## Sources

- Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), Theorem 3.1, Theorem 7.5 and Section 12.
