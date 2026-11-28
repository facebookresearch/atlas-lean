# Checking TO-security of finite-state systems is undecidable

Whether a finite-state deterministic system is TO-secure for an intransitive information flow policy is undecidable, although the related notions of purge-based security, IP-security and TA-security can be checked in polynomial time.

**Theorem.** There is no algorithm that decides, given a finite-state machine $M$ and a noninterference policy $\rightarrowtail$, whether $M$ is [TO-secure](to-security-for-intransitive-policies.md) with respect to $\rightarrowtail$.

## Depends on

- [TO-security for intransitive information flow policies](to-security-for-intransitive-policies.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces from the Post correspondence problem over an alphabet with at least two letters. From an instance $(U_1, \dots, U_n)$, $(W_1, \dots, W_n)$ it builds a finite-state machine for the policy on domains $A, B, C, D$ with $A \rightarrowtail C$, $A \rightarrowtail D$, $B \rightarrowtail C$ and $C \rightarrowtail D$ (plus reflexivity). Domain $A$ guesses a word letter by letter; $B$ chooses whether it is to be compared with a sequence of $U_i$ or of $W_i$ and guesses the indices; $C$ observes the indices and declares when the word is complete; $D$ observes nothing until then and afterwards observes whether $A$'s word matches $B$'s index sequence. The machine is built so that the security condition holds for $A$, $B$ and $C$, so whether it is TO-secure depends only on how $D$'s observations relate to the actions and views of $A$ and $C$; the source shows that it fails to be TO-secure exactly when the instance has a solution. Theorem 4 of the extended version states the result already for a fixed policy with four domains, so the undecidability does not come from complex policies. It deduces from it that no first-order unwinding conditions on binary relations over states can be sound and complete for TO-security, since such conditions can be checked in polynomial time. It also shows, by a reduction from TO-security, that the variant ITO-security is undecidable. For the same machine model, P-security, IP-security and TA-security are decidable in polynomial time, and even in nondeterministic logarithmic space.

## Sources

- Sebastian Eggert, Ron van der Meyden, Henning Schnoor and Thomas Wilke, "The Complexity of Intransitive Noninterference", in *2011 IEEE Symposium on Security and Privacy (S&P 2011)*, IEEE Computer Society, 2011, pp. 196–211, <https://doi.org/10.1109/SP.2011.30>, whose abstract states that checking TO-security is undecidable; read as the extended version arXiv:1308.1204v1, "Complexity and Unwinding for Intransitive Noninterference", <https://arxiv.org/abs/1308.1204v1>: Theorem 4 in Section 5.5 ("TO-security") with its proof, and Theorem 5 in Section 5.6 ("ITO-security"), in the numbering of that version.
