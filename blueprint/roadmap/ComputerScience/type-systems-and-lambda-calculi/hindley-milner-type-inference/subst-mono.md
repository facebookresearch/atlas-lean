# Term substitution for a `λ`-bound name

Let $\Gamma$ be a context that does not bind the
name $x$, with $\Gamma \vdash v : \tau_1$ and $\Gamma, x : \tau_1 \vdash e : \tau$, where no
binder name of $e$ is a free name of $v$. Then $\Gamma \vdash e[x := v] : \tau$.
