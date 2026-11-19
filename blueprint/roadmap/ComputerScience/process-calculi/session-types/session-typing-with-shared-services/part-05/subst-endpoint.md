# Runtime typing under substitution of a transmitted endpoint

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $b$ a
name scoped at depth $n$ that is not a declared trigger $\mathrm{c}_s$, $r$ a polarity, $c$, $v$
capabilities with $v \approx c$ and $p$ a process, with $b^{r}$ not in the domain of $\Delta$. If
$\Gamma; (\uparrow_0\Delta)[\mathrm{v}_0^{r} \mapsto c] \vdash_{n+1} p$, then $\Gamma; \Delta[b^{r}
\mapsto v] \vdash_n p\{b\}$.
