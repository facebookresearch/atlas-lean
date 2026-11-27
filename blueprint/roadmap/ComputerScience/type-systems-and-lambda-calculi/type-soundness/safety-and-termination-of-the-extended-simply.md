# Safety and termination of the extended simply typed lambda calculus

Extend the simply typed lambda calculus with the unit type and $\langle\rangle$, binary products with pairing $\langle e_1, e_2 \rangle$ and
projections $e \cdot l$, $e \cdot r$, binary sums with injections $l \cdot e$, $r \cdot e$ and case analysis, and $\mathbf{let}$. Booleans are the sum
$\mathrm{unit} + \mathrm{unit}$, with conditionals given by case analysis, and $\mathbf{let}\ x\ \mathbf{be}\ e_1\ \mathbf{in}\ e_2$ evaluates $e_1$ to a value and
substitutes it for $x$. Use the eager (call-by-value) dynamics, in which pairs and injections are values only when their components
are values. Then:

- **Preservation.** If $e : \tau$ and $e \mapsto e'$, then $e' : \tau$.
- **Progress.** If $e : \tau$ is closed, then either $e$ is a value or $e \mapsto e'$ for some $e'$.
- **Termination.** Every closed well-typed term reaches a value in finitely many steps.

Termination follows from strong normalization: every term of the simply typed lambda calculus with products is strongly normalizable,
by Tait's reducibility method, and strong normalization also holds with sums. Alternatively, encode $U + V$ in System F as
$\Pi X.\, (U \to X) \to (V \to X) \to X$, under which each case reduction is simulated by $\beta$-reductions, and use strong normalization of
System F. Call-by-value evaluation is one particular reduction sequence, so it terminates.

## Proof depends on

- [Progress for closed STLC terms](../operational-semantics-of-the-simply-typed-lambda/progress.md)
- [Termination of the call-by-value simply typed lambda calculus](../normalization-of-the-simply-typed-lambda-calculu/terminates-closed.md)
- [Strong normalization of System F](../normalization-and-logical-relations/strong-normalization-of-system-f.md)

## Sources

- R. Harper, *Practical Foundations for Programming Languages*, Cambridge University Press, 2012 (draft edition of 2012): Chapter 11 (statics and eager dynamics of nullary and binary products, rules 11.2a–11.2h, Theorem 11.1), Chapter 12 (sums, Theorems 12.1–12.2, and booleans as $\mathrm{unit} + \mathrm{unit}$, equation 12.7a), Chapter 4 (the definition form $\mathrm{let}(e_1; x.e_2)$). The second edition, Cambridge University Press, 2016, states the same safety results as Theorems 10.1 and 11.1–11.2.
- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989: Chapter 6 (strong normalization with products, Section 6.3.3), Section 10.5 (strong normalization also holds with sums) and Section 11.3.4 (sums in System F and simulation of their reductions).
