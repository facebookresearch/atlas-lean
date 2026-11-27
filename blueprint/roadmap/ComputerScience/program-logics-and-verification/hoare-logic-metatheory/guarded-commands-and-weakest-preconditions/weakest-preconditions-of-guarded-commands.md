# Weakest preconditions of guarded commands

Predicates are Boolean functions on the state space; $T$ holds in every state and $F$ in none. For a statement $S$ of the [guarded command language](guarded-commands.md) and a predicate $R$, the *weakest precondition* $\mathrm{wp}(S, R)$ is the weakest predicate on initial states such that every activation of $S$ is guaranteed to terminate properly in a final state satisfying $R$. It is fixed by the following clauses, where $R^x_E$ is $R$ with every occurrence of $x$ replaced by $(E)$, and $IF$, $DO$ and $BB$ are formed from the same guarded commands $B_i \to SL_i$, $1 \le i \le n$:

- $\mathrm{wp}(\mathbf{skip}, R) = R$ and $\mathrm{wp}(x := E, R) = R^x_E$;
- $\mathrm{wp}(S_1 ; S_2, R) = \mathrm{wp}(S_1, \mathrm{wp}(S_2, R))$;
- $\mathrm{wp}(IF, R) = BB \wedge \forall i \in \{1, \dots, n\}.\ (B_i \Rightarrow \mathrm{wp}(SL_i, R))$;
- with $H_0(R) = R \wedge \neg BB$ and $H_k(R) = \mathrm{wp}(IF, H_{k-1}(R)) \vee H_0(R)$ for $k > 0$, $\mathrm{wp}(DO, R) = \exists k \ge 0.\ H_k(R)$; here $H_k(R)$ is the weakest precondition guaranteeing proper termination after at most $k$ selections of a guarded list, in a state satisfying $R$.

Dijkstra requires of every statement $S$ and all predicates $P, Q$ that, in every state,

1. $\mathrm{wp}(S, F) = F$ (the law of the excluded miracle);
2. if $P \Rightarrow Q$ in every state, then $\mathrm{wp}(S, P) \Rightarrow \mathrm{wp}(S, Q)$;
3. $\mathrm{wp}(S, P) \wedge \mathrm{wp}(S, Q) = \mathrm{wp}(S, P \wedge Q)$;
4. $\mathrm{wp}(S, P) \vee \mathrm{wp}(S, Q) \Rightarrow \mathrm{wp}(S, P \vee Q)$.

In particular $\mathrm{wp}(S, T)$ is the weakest precondition guaranteeing proper termination of $S$. For an integer-valued function $t$ on states, $\mathrm{wdec}(S, t)$ is the weakest precondition such that $S$ is guaranteed to terminate properly in a state in which the value of $t$ is at least $1$ smaller than in the initial state. For nondeterministic statements $\mathrm{wp}$ does not determine the possible final states of initial states from which termination is not guaranteed.

## Depends on

- [Guarded commands](guarded-commands.md)

## Sources

- E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs", *Communications of the ACM* 18(8):453–457, 1975; author's manuscript EWD472, <https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF>, Sections 3.1–3.3.
