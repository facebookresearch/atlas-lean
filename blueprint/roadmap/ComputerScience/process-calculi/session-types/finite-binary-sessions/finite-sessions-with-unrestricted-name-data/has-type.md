# Linear session typing of sequential threads

The judgment $\Gamma \vdash_n p$, for a natural number $n$ (the number of enclosing input binders),
a session context $\Gamma$ and a π-calculus process $p$, is defined inductively by three rules.

- If $\Gamma(c) = \mathrm{end}$ for every channel number $c$, then $\Gamma \vdash_n \mathbf{0}$.
- If $\Gamma(a) = {!S}$, the name $b$ is in scope at depth $n$ (a free constant, or a variable with
  index $< n$) and $\Gamma[a \mapsto S] \vdash_n p$, then $\Gamma \vdash_n
  \overline{\mathrm{c}_a}\langle b\rangle.p$.
- If $\Gamma(a) = {?S}$ and $\Gamma[a \mapsto S] \vdash_{n+1} p$, then $\Gamma \vdash_n
  \mathrm{c}_a(\cdot).p$.

Here $\mathrm{c}_a$ is the free channel constant numbered $a$, the input $\mathrm{c}_a(\cdot).p$
binds de Bruijn index $0$ in $p$, and $\Gamma[a \mapsto S]$ replaces the entry of $\Gamma$ at $a$ by
$S$. Subjects are always free constants; a received name is passive data and never becomes a session
subject. No other process form is typable.
