# Algorithm W

Given a typing context $\Gamma$, an expression $e$ and a counter $n$,
Algorithm W either fails or returns a substitution, a monotype and a new counter; type variables
$\alpha_m$ with $m \ge n$ serve as fresh. Write $\tau_1 \to \tau_2$ for the arrow type, $s\Gamma$
for $\Gamma$ with the substitution $s$ applied to every type scheme, and $s(\tau)$ for $s$
applied to a monotype $\tau$. Algorithm W is defined by recursion on $e$, and fails as soon
as a recursive call or a unification fails:

- For a variable $x$: if $x$ is unbound in $\Gamma$, W fails; otherwise, with $\sigma$ the
  visible type scheme of $x$, W returns the identity substitution, the instance of $\sigma$
  that replaces each bound variable $i$ by $\alpha_{n+i}$, and the counter $n + k$, where $k$
  is one more than the largest bound-variable index of $\sigma$ ($0$ if it has none).
- For $\lambda x.\, e'$: W runs on the context $\Gamma$ with $x$ bound in front to the
  monotype $\alpha_n$, the body $e'$ and the counter $n + 1$; if this returns
  $(s, \tau, n')$, W returns $(s, s(\alpha_n) \to \tau, n')$.
- For an application $e_1\, e_2$: W runs on $\Gamma$, $e_1$, $n$, giving
  $(s_1, \tau_1, n_1)$, then on $s_1\Gamma$, $e_2$, $n_1$, giving $(s_2, \tau_2, n_2)$, then
  runs unification on the single equation $s_2(\tau_1) = \tau_2 \to \alpha_{n_2}$, giving
  $s_3$; it returns the composite substitution applying $s_1$, then $s_2$, then $s_3$, the
  type $s_3(\alpha_{n_2})$ and the counter $n_2 + 1$.
- For $\mathtt{let}\ x = e_1\ \mathtt{in}\ e_2$: W runs on $\Gamma$, $e_1$, $n$, giving
  $(s_1, \tau_1, n_1)$, then on the context $s_1\Gamma$ with $x$ bound in front to the
  generalization of $\tau_1$ in $s_1\Gamma$, $e_2$ and $n_1$, giving $(s_2, \tau_2, n_2)$;
  it returns the composite substitution applying $s_1$ then $s_2$, the type $\tau_2$ and the
  counter $n_2$.
