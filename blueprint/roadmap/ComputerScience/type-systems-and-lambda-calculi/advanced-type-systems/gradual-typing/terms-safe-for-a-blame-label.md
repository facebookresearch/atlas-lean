# Terms safe for a blame label

For a blame label $p$, the relation *$t$ safe for $p$* on terms of the [blame calculus](the-blame-calculus-and-its-subtyping-relations.md) holds when every cast labeled $p$ is a
positive subtyping, every cast labeled $\bar p$ is a negative subtyping, and every subset-type test labeled $p$ succeeds. It is defined by the rules:

- variables and constants are safe for $p$; $\lambda x{:}S.\, t$ and $t\, s$ are safe for $p$ when their immediate subterms are;
- $\langle T \Leftarrow S \rangle^p\, s$ is safe for $p$ if $S <:^+ T$ and $s$ is safe for $p$; $\langle T \Leftarrow S \rangle^{\bar p}\, s$ is safe for $p$ if $S <:^- T$ and $s$ is safe for $p$;
  $\langle T \Leftarrow S \rangle^q\, s$ is safe for $p$ if $p \ne q$, $\bar p \ne q$ and $s$ is safe for $p$;
- a dynamic value $\mathrm{Dyn}_G(v)$ is safe for $p$ if $v$ is;
- an active check that a value $v$ satisfies a subset type $\{x : B \mid t\}$, with test term $s$ and label $p$, is safe for $p$ if $s \longrightarrow^* \mathrm{true}$; one with label $q \ne p$ is safe
  for $p$ if $s$ is.

## Depends on

- [The blame calculus and its subtyping relations](the-blame-calculus-and-its-subtyping-relations.md)

## Sources

- P. Wadler and R. B. Findler, "Well-typed programs can't be blamed", *European Symposium on Programming (ESOP 2009)*, LNCS 5502, 1–16, <https://doi.org/10.1007/978-3-642-00590-9_1>: Section 4, Figure 7 (safe terms) and the paragraph before Proposition 9.
