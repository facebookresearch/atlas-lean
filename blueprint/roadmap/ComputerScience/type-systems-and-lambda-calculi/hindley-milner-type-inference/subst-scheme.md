# Term substitution for a scheme

Let $\Gamma$ be a context that does not bind the name
$x$, let $\sigma$ be a scheme such that $\Gamma \vdash v : \tau'$ for every instance $\tau'$ of
$\sigma$, and let $\Gamma, x : \sigma \vdash e : \tau$, where no binder name of $e$ is a free
name of $v$. Then $\Gamma \vdash e[x := v] : \tau$.
