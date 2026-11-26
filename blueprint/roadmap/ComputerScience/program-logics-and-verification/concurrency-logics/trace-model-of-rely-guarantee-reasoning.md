# Trace model of rely-guarantee reasoning

Commands over a state set $\Sigma$ are $\mathbf{basic}\ f$ (for $f : \Sigma \to \Sigma$), $C_1; C_2$, $\mathbf{if}\ b\ \mathbf{then}\ C_1\ \mathbf{else}\ C_2$,
$\mathbf{while}\ b\ \mathbf{do}\ C$ and $\mathbf{await}\ b\ \mathbf{then}\ C$, with $b \subseteq \Sigma$. A *configuration* is a pair $(P, s)$ of an optional
command ($P = \mathrm{None}$ means terminated) and a state $s \in \Sigma$. A *program step* $(P, s) \xrightarrow{c} (P', s')$ is given by the
usual small-step rules, where $\mathbf{await}\ b\ \mathbf{then}\ C$ executes $C$ to termination in one step from a state in $b$. An
*environment step* $(P, s) \xrightarrow{e} (P, s')$ changes the state arbitrarily and leaves the command unchanged.

- A *computation* is a finite nonempty sequence of configurations in which each consecutive pair is a program step
  or an environment step.
- For a precondition $\mathit{pre} \subseteq \Sigma$ and a rely relation $R \subseteq \Sigma \times \Sigma$, $\mathrm{assum}(\mathit{pre}, R)$ is the set of
  computations whose first state is in $\mathit{pre}$ and whose environment steps $(P, s) \xrightarrow{e} (P, s')$ all satisfy
  $(s, s') \in R$.
- For a guarantee relation $G$ and a postcondition $\mathit{post}$, $\mathrm{comm}(G, \mathit{post})$ is the set of computations whose
  program steps $(P, s) \xrightarrow{c} (P', s')$ all satisfy $(s, s') \in G$ and whose last configuration, if it has command
  $\mathrm{None}$, has state in $\mathit{post}$.
- An assertion $p \subseteq \Sigma$ is *stable* under $R$ if $s \in p$ and $(s, s') \in R$ imply $s' \in p$.
- A command $C$ *satisfies* $(\mathit{pre}, R, G, \mathit{post})$ if every computation starting from $(C, s)$, for any $s$, that lies
  in $\mathrm{assum}(\mathit{pre}, R)$ also lies in $\mathrm{comm}(G, \mathit{post})$.

For a list $C_1, \dots, C_n$ of parallel components, configurations are a list of optional commands with one state, a
program step is a program step of one component, an environment step changes only the state, and assumptions,
commitments and satisfaction are defined in the same way, with termination meaning that every component is
$\mathrm{None}$.

## Sources

- L. Prensa Nieto, *Hoare Logic for Parallel Programs*, Isabelle/HOL theory library (HOL-Hoare_Parallel), document of May 23, 2024, Sections 3.1–3.3 (definitions of etran, ctran, cptn, assum, comm, com-validity, par-assum, par-comm, par-com-validity) and Section 3.4.1 (stable).
- P. Aczel, *On an inference rule for parallel composition*, unpublished note, University of Manchester, 1983.
- K. R. Apt, F. S. de Boer and E.-R. Olderog, *Verification of Sequential and Concurrent Programs*, 3rd ed., Springer, 2009.
