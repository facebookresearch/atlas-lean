# Lazy sampling equals eager sampling

Let $(f_\omega)_{\omega \in \Omega}$ be a family of functions $X \to Y$ indexed by a finite nonempty
set, let $\nu_T(x)$ be fresh-answer distributions, and let $I$ be a property of tables such that:

- every table satisfying $I$ has a nonempty consistent set;
- for every table $T$ satisfying $I$ and every query $x$ that $T$ does not record, drawing $\omega$
  uniformly from the consistent set of $T$ is the same as drawing $y$ from $\nu_T(x)$ and then
  drawing $\omega$ uniformly from the consistent set of $T$ extended by $x \mapsto y$;
- recording a possible fresh answer preserves $I$.

Then for every adaptive oracle computation $c$ and every table $T$ satisfying $I$, the output of $c$
run against the lazily sampled oracle from $T$ is distributed as the output of $c$ run against
$f_\omega$, for $\omega$ drawn uniformly from the consistent set of $T$.
