# Clock regions of timed automata

Let $C$ be a finite set of clocks of a timed automaton whose clock constraints compare clocks with integer constants,
and for each $x \in C$ let $c_x$ be the largest integer $c$ such that $x \le c$ or $c \le x$ is a subformula of some clock constraint,
assuming every clock occurs in some constraint and all constants are nonnegative integers, as clock values are nonnegative. For $t \in \mathbb{R}_{\ge 0}$ write $\lfloor t \rfloor$ for its integral part and $\mathrm{fract}(t)$ for its
fractional part. Clock valuations $\nu, \nu' : C \to \mathbb{R}_{\ge 0}$ are *region equivalent*, $\nu \sim \nu'$, when:

1. for all $x \in C$, either both $\nu(x) > c_x$ and $\nu'(x) > c_x$, or both $\nu(x) \le c_x$ and $\nu'(x) \le c_x$ and $\lfloor \nu(x) \rfloor = \lfloor \nu'(x) \rfloor$;
2. for all $x, y \in C$ with $\nu(x) \le c_x$ and $\nu(y) \le c_y$, $\mathrm{fract}(\nu(x)) \le \mathrm{fract}(\nu(y))$ if and only if
   $\mathrm{fract}(\nu'(x)) \le \mathrm{fract}(\nu'(y))$;
3. for all $x \in C$ with $\nu(x) \le c_x$, $\mathrm{fract}(\nu(x)) = 0$ if and only if $\mathrm{fract}(\nu'(x)) = 0$.

A *clock region* is an equivalence class of $\sim$. Equivalent valuations satisfy the same clock constraints, and the number of
clock regions is at most $|C|! \cdot 2^{|C|} \cdot \prod_{x \in C} (2 c_x + 2)$.

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Definition 4.3, the remark after Example 4.4 that equivalent valuations satisfy the same constraints, and Lemma 4.5 (bound on the number of regions).
