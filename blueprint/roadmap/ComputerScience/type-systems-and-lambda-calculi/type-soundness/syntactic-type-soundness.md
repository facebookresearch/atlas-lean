# Syntactic type soundness

Let a language have closed programs with a one-step evaluation relation $\mapsto$ (with reflexive-transitive closure $\mapsto^{*}$), a set of values, a set of *faulty* programs (in Wright and Felleisen's languages, programs with a subexpression on which evaluation is undefined, such as a constant applied outside its domain), and a typing judgment $\vdash e : \tau$. A closed program $e$ *diverges*, written $e \Uparrow$, if every program reachable from $e$ by $\mapsto^{*}$ can take a further step. Suppose that

- *subject reduction*: if $\vdash e : \tau$ and $e \mapsto e'$, then $\vdash e' : \tau$;
- *uniform evaluation*: for every closed $e$ that never reduces to a faulty program, either $e \Uparrow$ or $e \mapsto^{*} v$ for a value $v$; and
- *faulty programs are untypable*: if $e$ is faulty, there is no $\tau$ with $\vdash e : \tau$.

Then *syntactic soundness* holds: if $\vdash e : \tau$, then either $e \Uparrow$ or $e \mapsto^{*} v$ for a value $v$ with $\vdash v : \tau$. Indeed, by subject reduction every program reachable from $e$ has type $\tau$, so none is faulty, and uniform evaluation applies. Syntactic soundness implies *weak soundness*, that the evaluation of a well-typed program does not yield the type error $\mathrm{wrong}$.

## Sources

- A. K. Wright and M. Felleisen, "A syntactic approach to type soundness", *Information and Computation* 115(1):38–94, 1994; technical report TR91-160, Rice University, <https://www.cs.rice.edu/CS/PLT/Publications/Scheme/ic94-wf.ps.gz>, Section 1 (weak and strong soundness) and Section 4, Lemma 4.10, Main Lemma 4.11 and Theorem 4.12
