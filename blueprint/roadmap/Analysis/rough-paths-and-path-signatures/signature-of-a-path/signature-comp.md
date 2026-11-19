# Reparametrisation invariance of the signature

Let every component of the velocity $v$ of $X$ be continuous and let $\psi : \mathbb{R} \to
\mathbb{R}$ be differentiable with continuous derivative $\psi'$. The reparametrised path
$\tilde X_u = X_{\psi(u)}$ has velocity $\tilde v^i(u) = v^i(\psi(u))\,\psi'(u)$, and for all reals
$s, t$ and every word,

$$S(\tilde X)^w_{s,t} = S(X)^w_{\psi(s),\,\psi(t)} .$$

When $\psi$ is an increasing map of $[a, b]$ onto itself, this is the invariance of the signature
under time reparametrisation: the signature sees the trace of the path and the order in which it
is traversed, not its speed. The identity holds for every continuously differentiable $\psi$,
monotone or not, because the integrals are oriented.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, §1.3.1 (invariance under time reparametrisation).
- T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
  arXiv:1405.4537, Lemma 4.1 (the same invariance for controlled differential equations).
