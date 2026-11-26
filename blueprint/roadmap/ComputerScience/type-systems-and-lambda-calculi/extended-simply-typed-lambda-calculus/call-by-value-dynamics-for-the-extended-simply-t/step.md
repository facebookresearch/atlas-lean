# Small-step call-by-value reduction in the extended calculus

One-step reduction on terms
of type $A$ in a context $\Gamma$ is the least relation closed under the following eager,
left-to-right rules, where $b[a]$ is the result of substituting $a$ for the newest free variable
of $b$:

* functions (rules (8.5b–d)): reduce the function of an application; once it is a value, reduce
  the argument; and $(\lambda b)\,a$ reduces to $b[a]$ when $a$ is a value;
* products (rules (10.2c–h)): reduce the left component of a pair, then the right component once
  the left one is a value; reduce the argument of a projection; and $\mathsf{fst}\,\langle a,
  b\rangle$ and $\mathsf{snd}\,\langle a, b\rangle$ reduce to $a$ and $b$ when $a$ and $b$ are
  values;
* sums (rules (11.2d–h)): reduce the payload of an injection; reduce the scrutinee of a case
  analysis; and $\mathsf{case}\,(\mathsf{inl}\,a)\,l\,r$ reduces to $l[a]$ and
  $\mathsf{case}\,(\mathsf{inr}\,b)\,l\,r$ to $r[b]$ when the payload is a value;
* booleans (rules (11.6c–e)): reduce the condition of a conditional, and
  $\mathsf{ite}\,\mathsf{tt}\,t\,e$ and $\mathsf{ite}\,\mathsf{ff}\,t\,e$ reduce to $t$ and $e$;
* `let` (rules (5.4g,h)): reduce the bound term, and $\mathsf{let}\,a\,b$ reduces to $b[a]$ when
  $a$ is a value.

The rule numbers are those of Harper's *Practical Foundations for Programming Languages*,
2nd ed., with the bracketed rules and premises of the eager dynamics. No rule reduces under a
binder or inside the branches of a conditional or case analysis.

Both sides of every rule are terms of type $A$ in $\Gamma$, so preservation holds by
construction: `Step` is closed under the typing of the calculus because a rule is accepted by
the type checker only when its right-hand side has the type of its left-hand side. The content of
type safety is therefore progress, `Step.progress`, together with this intrinsic closure; the
multi-step corollaries apply progress at every reachable term.
