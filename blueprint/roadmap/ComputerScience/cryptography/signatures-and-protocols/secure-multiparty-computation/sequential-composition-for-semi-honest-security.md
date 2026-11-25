# Sequential composition for semi-honest security

An *oracle-aided* two-party protocol is an ordinary protocol in which the parties may also invoke an oracle, one call at a time: the requesting party writes a query $q_1$, the other party writes a query $q_2$, and the oracle writes an answer for each party. The protocol *uses the oracle-functionality* $f$ if each answer pair is distributed as $f(q_1, q_2)$, the requesting party receiving $f_1(q_1, q_2)$, and the length of every query is polynomially related to the length of the initial input. An oracle-aided protocol using $f$ *privately computes* $g$ if there are polynomial-time simulators satisfying the definition of privately computing $g$ for the views of the oracle-aided execution, and it then *privately reduces* $g$ to $f$.

**Composition theorem.** If $g$ is privately reducible to $f$ and some protocol privately computes $f$, then some protocol privately computes $g$: replacing each oracle call of the reduction by an execution of the protocol for $f$ gives such a protocol. More generally, if $g$ is privately reducible to $f$ and $f$ to $e$, then $g$ is privately reducible to $e$.

## Depends on

- [Two-party security against semi-honest adversaries](two-party-security-against-semi-honest.md)

## Sources

- O. Goldreich, *Foundations of Cryptography*, vol. 2: Basic Applications, Cambridge University Press, 2004; draft chapter "General Protocols", posted version 3.2, 2003, <https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/prot.pdf>, Definitions 7.3.1 and 7.3.2 and Theorem 7.3.3 with the remark following it
