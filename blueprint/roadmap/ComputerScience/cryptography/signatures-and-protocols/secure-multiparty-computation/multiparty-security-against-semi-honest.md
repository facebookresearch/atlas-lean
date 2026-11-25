# Multiparty security against semi-honest adversaries

Let $\pi$ be an $n$-party protocol and $F$ an $n$-party functionality, with security parameter $\kappa$; inputs $x_1, \dots, x_n$ range over strings of length polynomial in $\kappa$, and the distributions below are ensembles indexed by $\kappa$ and the inputs. The *view* of a party consists of its private input,
its random tape and the list of all messages it received during the protocol. For a set $C$ of corrupted parties and inputs $x_1, \dots, x_n$, and a simulator
$\mathrm{Sim}$, define:

- $\mathrm{Real}_\pi(\kappa, C; x_1, \dots, x_n)$: run $\pi$ with every party $P_i$ following the protocol on input $x_i$; with $V_i$ the final view and $y_i$ the
  final output of $P_i$, output $(\{V_i : i \in C\}, (y_1, \dots, y_n))$;
- $\mathrm{Ideal}_{F,\mathrm{Sim}}(\kappa, C; x_1, \dots, x_n)$: compute $(y_1, \dots, y_n) \leftarrow F(x_1, \dots, x_n)$ and output $(\mathrm{Sim}(C, \{(x_i, y_i) : i \in C\}), (y_1, \dots, y_n))$.

The protocol $\pi$ *securely realizes $F$ in the presence of semi-honest adversaries* if there is a probabilistic polynomial-time simulator $\mathrm{Sim}$ such that for every set $C$ of corrupted
parties and all inputs, the two distributions are computationally indistinguishable in $\kappa$. It does so *against $t$ corrupted parties* if this holds for every
$C$ with $|C| \le t$. Including all parties' outputs builds correctness into the definition, also for randomized $F$.

For $n = 2$ this is the setting of two-party semi-honest security; the precise correspondence between the two definitions (views, transcripts and
security-parameter conventions) is a separate statement.

## Depends on

- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)

## Sources

- D. Evans, V. Kolesnikov and M. Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*, Foundations and Trends in Privacy and Security 2(2–3), 2018, <https://securecomputation.org/docs/pragmaticmpc.pdf>: Section 2.3.2 (views, the Real and Ideal distributions, Definition 2.2 and the remark on including outputs) and Section 3.3 (security against $t$ corrupted parties).
