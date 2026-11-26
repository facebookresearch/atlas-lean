# Late transition semantics of the π-calculus

The agents of the π-calculus are given by
$$P ::= 0 \mid \bar x y . P \mid x(y) . P \mid \tau . P \mid (y) P \mid [x = y] P \mid P \mid Q \mid P + Q \mid A(y_1, \dots, y_n),$$
where $x(y)$ and the restriction $(y)$ bind $y$, and each agent identifier $A$ has one defining equation $A(x_1, \dots, x_n) \overset{\mathrm{def}}{=} P$ with $\mathrm{fn}(P) \subseteq \{x_1, \dots, x_n\}$. Substitution $P\sigma$ renames bound names to avoid capture, and alpha-convertible agents are identified. The actions are the silent action $\tau$, free outputs $\bar x y$, inputs $x(y)$ and bound outputs $\bar x(y)$; in the last two $y$ is bound, $\mathrm{bn}(\alpha)$ is the set of bound names of $\alpha$ and $\mathrm{n}(\alpha)$ the set of all its names. The transitions are the least relations closed under the following rules, those for $+$ and $\mid$ also in symmetric form.

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

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>: Section 1.1 (Definitions 1–7: agents, binding, defining equations, substitution, alpha-conversion), Section 1.2 and Table 1 (actions), Section 1.3, Definition 8 and Table 2 (the rules of action), and the discussion of late instantiation after Table 2.
