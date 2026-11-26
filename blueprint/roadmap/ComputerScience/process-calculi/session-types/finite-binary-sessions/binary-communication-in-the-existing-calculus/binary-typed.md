# Dual session typing of a binary configuration

Let $\Gamma$ be a session context (a function assigning a finite session type to every channel
number) and $(p,q)$ a pair of π-calculus processes. The pair is binary typed in $\Gamma$ when
$\Gamma \vdash_0 p$ and $\overline{\Gamma} \vdash_0 q$, where $\overline{\Gamma}(c)$ is the dual of
$\Gamma(c)$ for every channel number $c$.

Here $\Gamma \vdash_n p$ is linear typing of sequential threads with $n$ enclosing input binders:
$\mathbf{0}$ is typed when every entry of $\Gamma$ is $\mathrm{end}$;
$\overline{\mathrm{c}_a}\langle b\rangle.p$ when $\Gamma(a) = {!S}$, the name $b$ is in scope at
depth $n$ and $\Gamma[a \mapsto S] \vdash_n p$; and $\mathrm{c}_a(\cdot).p$ when $\Gamma(a) = {?S}$
and $\Gamma[a \mapsto S] \vdash_{n+1} p$. The two threads thus own opposite roles on every channel;
this alone does not exclude the two threads waiting on each other on different channels.
