# Refinement mappings prove implementation

In the framework of Abadi and Lamport, a state space is a set $\Sigma \subseteq \Sigma_E \times \Sigma_I$ of pairs of an externally visible and an internal component, with $\Pi_E$ the projection to the visible component. A *specification* $S = (\Sigma, F, N, L)$ consists of a state machine, with initial states $F \subseteq \Sigma$ and next-state relation $N \subseteq \Sigma \times \Sigma$, and a *supplementary property* $L$, a set of behaviors. Its *machine property* $M$ consists of the infinite sequences $s_0 s_1 \dots$ with $s_0 \in F$ and, for every $i$, $(s_i, s_{i+1}) \in N$ or $s_{i+1} = s_i$; its property is $M \cap L$; and the externally visible property it defines is the closure under adding and removing stuttering steps of $\Pi_E(M \cap L)$. A specification $S_1$ *implements* $S_2$ if the externally visible property defined by $S_1$ is contained in that defined by $S_2$.

A *refinement mapping* from $S_1 = (\Sigma_1, F_1, N_1, L_1)$ to $S_2 = (\Sigma_2, F_2, N_2, L_2)$ is a map $f : \Sigma_1 \to \Sigma_2$ such that

1. $\Pi_E(f(s)) = \Pi_E(s)$ for every $s \in \Sigma_1$;
2. $f(F_1) \subseteq F_2$;
3. if $(s, t) \in N_1$ then $(f(s), f(t)) \in N_2$ or $f(s) = f(t)$;
4. $f$ maps every behavior in the property of $S_1$ to a behavior in $L_2$.

If there is a refinement mapping from $S_1$ to $S_2$, then $S_1$ implements $S_2$.

## Sources

- M. Abadi and L. Lamport, "The existence of refinement mappings", *Proceedings of the Third Annual Symposium on Logic in Computer Science (LICS 1988)*, IEEE, 1988, Section 2, conditions R1–R4 and Proposition 1
- Journal version: M. Abadi and L. Lamport, "The existence of refinement mappings", *Theoretical Computer Science* 82(2):253–284, 1991.
