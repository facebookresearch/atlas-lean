# Valid

Let $v \colon \mathbb{N} \to \{\mathrm{true}, \mathrm{false}\}$ be a valuation and let $\Gamma$ and $\Delta$ be finite lists of propositional formulas. The sequent $\Gamma \vdash \Delta$ is true under $v$ if, whenever every formula of $\Gamma$ evaluates to true under $v$, some formula of $\Delta$ evaluates to true under $v$. In particular a sequent with empty $\Delta$ is true under $v$ only if some formula of $\Gamma$ is false under $v$.
