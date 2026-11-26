# Late transition semantics of the π-calculus

Fix an infinite set of names, ranged over by $x, y, z, u, v, w$, and a set of agent identifiers, each with an arity $n \ge 0$. The agents of the π-calculus are given by

$$P ::= 0 \mid \bar x y . P \mid x(y) . P \mid \tau . P \mid (y) P \mid [x = y] P \mid P \mid Q \mid P + Q \mid A(y_1, \dots, y_n),$$

where in $x(y) . P$ and $(y) P$ the occurrence of $y$ in parentheses binds $y$ with scope $P$, and $\mathrm{fn}(P)$ is the set of names with a free occurrence in $P$. Each agent identifier $A$ of arity $n$ has exactly one defining equation $A(x_1, \dots, x_n) \overset{\mathrm{def}}{=} P$, with $x_1, \dots, x_n$ pairwise distinct and $\mathrm{fn}(P) \subseteq \{x_1, \dots, x_n\}$. The set $\mathrm{bn}(P)$ contains every name with a bound occurrence in $P$, with $\mathrm{bn}(A(x_1, \dots, x_n)) = \mathrm{bn}(P)$ for the defining equation, and the defining equations are such that $\mathrm{bn}(A(x_1, \dots, x_n))$ is finite for every $A$; $\mathrm{n}(P) = \mathrm{fn}(P) \cup \mathrm{bn}(P)$, and $\mathrm{n}(P, Q, \dots)$ is the union for several agents. A *substitution* is a map $\sigma$ from names to names that is the identity on all but finitely many names; $\{y_1/x_1, \dots, y_n/x_n\}$, or $\{\tilde y / \tilde x\}$, maps each $x_i$ to $y_i$ and fixes the other names. $P\sigma$ replaces simultaneously every free occurrence of each name $z$ by $z\sigma$, renaming bound names to avoid capture: $(x(y) . P)\sigma = x\sigma(y') . P\{y'/y\}\sigma$ and $((y) P)\sigma = (y') P\{y'/y\}\sigma$, where $y'$ is the first name, in a fixed enumeration of the names, with $y' \notin \mathrm{fn}((y) P, P\sigma)$ and $y'\sigma = y'$. Agents are not identified up to alpha-conversion: the rules below, $\mathrm{n}$ and the freshness conditions apply to agents as written. The actions are the silent action $\tau$, free outputs $\bar x y$, inputs $x(y)$ and bound outputs $\bar x(y)$; in the last two $y$ is bound, $\mathrm{bn}(\alpha)$ is the set of bound names of $\alpha$ and $\mathrm{n}(\alpha)$ the set of all its names. The transitions are the least relations closed under the following rules, those for $+$ and $\mid$ also in symmetric form.

- $\tau . P \xrightarrow{\tau} P$; $\bar x y . P \xrightarrow{\bar x y} P$; $x(z) . P \xrightarrow{x(w)} P\{w/z\}$ if $w \notin \mathrm{fn}((z)P)$.
- If $P \xrightarrow{\alpha} P'$ then $P + Q \xrightarrow{\alpha} P'$ and $[x = x] P \xrightarrow{\alpha} P'$.
- If $P\{\tilde y / \tilde x\} \xrightarrow{\alpha} P'$ and $A(\tilde x) \overset{\mathrm{def}}{=} P$, then $A(\tilde y) \xrightarrow{\alpha} P'$.
- If $P \xrightarrow{\alpha} P'$ and $\mathrm{bn}(\alpha) \cap \mathrm{fn}(Q) = \emptyset$, then $P \mid Q \xrightarrow{\alpha} P' \mid Q$.
- If $P \xrightarrow{\bar x y} P'$ and $Q \xrightarrow{x(z)} Q'$, then $P \mid Q \xrightarrow{\tau} P' \mid Q'\{y/z\}$.
- If $P \xrightarrow{\bar x(w)} P'$ and $Q \xrightarrow{x(w)} Q'$, then $P \mid Q \xrightarrow{\tau} (w)(P' \mid Q')$.
- If $P \xrightarrow{\alpha} P'$ and $y \notin \mathrm{n}(\alpha)$, then $(y) P \xrightarrow{\alpha} (y) P'$.
- If $P \xrightarrow{\bar x y} P'$, $y \ne x$ and $w \notin \mathrm{fn}((y)P')$, then $(y) P \xrightarrow{\bar x(w)} P'\{w/y\}$.

The input rule does not instantiate the received name, which is substituted only when a communication is inferred: this is the *late* scheme.

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>: Section 1.1 (the infinite set of names and Definitions 1–7: agents, binding, defining equations with pairwise distinct parameters, finite bound names of identifiers, substitutions that are almost everywhere the identity, and their application with change of bound names), Section 1.2 and Table 1 (actions), Section 1.3, Definition 8 and Table 2 (the rules of action), and the discussion of late instantiation after Table 2.
