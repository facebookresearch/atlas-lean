# Iso-recursive types: safety without normalization

Extend the simply typed lambda calculus with recursive types $\mu t.\tau$, where $t$ may occur in $\tau$, and the operations
$\mathrm{fold}(e) : \mu t.\tau$ for $e : [\mu t.\tau / t]\tau$ and $\mathrm{unfold}(e) : [\mu t.\tau / t]\tau$ for $e : \mu t.\tau$. The dynamics adds
$\mathrm{unfold}(\mathrm{fold}(e)) \mapsto e$ when $\mathrm{fold}(e)$ is a value, with $\mathrm{fold}(e)$ a value when $e$ is (eager interpretation) and search rules
under $\mathrm{fold}$ and $\mathrm{unfold}$. Then:

- **Safety.** If $e : \tau$ and $e \mapsto e'$ then $e' : \tau$, and if $e : \tau$ is closed then $e$ is a value or $e \mapsto e'$ for some $e'$.
- **No normalization.** For any type $\tau$, let $\sigma = \mu t.\, t \to \tau$ and $\omega = \lambda (x{:}\sigma).\, \mathrm{unfold}(x)(x) : \sigma \to \tau$. Then
  $\omega(\mathrm{fold}(\omega)) : \tau$ is closed and well typed, and $\omega(\mathrm{fold}(\omega)) \mapsto \mathrm{unfold}(\mathrm{fold}(\omega))(\mathrm{fold}(\omega)) \mapsto \omega(\mathrm{fold}(\omega))$, so its evaluation
  never terminates. More generally the type $\mathrm{self}(\tau) = \mu t.\, t \to \tau$ makes general recursion, and hence a fixed-point operator at every
  type, definable.

## Depends on

- [Progress for closed STLC terms](../operational-semantics-of-the-simply-typed-lambda/progress.md)

## Proof depends on

- [Syntactic type soundness](../type-soundness/syntactic-type-soundness.md)

## Sources

- R. Harper, *Practical Foundations for Programming Languages*, Cambridge University Press, 2012 (draft edition of 2012): Section 16.1 (rules 16.1–16.3, eager and lazy readings of $\mathrm{fold}$, Theorem 16.1) and Section 16.3 (self-referential types $\mathrm{self}(\tau) = \mathrm{rec}(t.\, t \to \tau)$ and the derivation of general recursion). The divergent term is derived on this page from that definition.
