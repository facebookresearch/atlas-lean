# Subject reduction, progress and type safety for synchronous multiparty sessions

Consider the synchronous multiparty session calculus with a single session. A multiparty session $M$ is a parallel composition $p_1 \triangleleft P_1 \mid \dots \mid p_n \triangleleft P_n$ of participants with their processes, and reduction is synchronous communication: a send by $p$ to $q$ of a label with a value meets the matching input of $q$ from $p$. Write $\vdash M : G$ when the participant names $p_1, \dots, p_n$ are pairwise distinct, every participant of $G$ is among them, $\mathrm{pt}(G) \subseteq \{p_1, \dots, p_n\}$, the global type $G$ is projectable onto every participant, and each process $P_i$ is typed by a subtype of the [projection](global-types-and-projection-in-multiparty.md) of $G$ onto $p_i$. A session is *stuck* if it is not structurally congruent to $p \triangleleft \mathbf{0}$ and cannot reduce.

- **Consumption.** For a global type $G$, the consumption $G \setminus p \xrightarrow{\ell} q$ of a communication is defined coinductively. If $G = p \to q : \{\ell_i(S_i).G_i\}_{i \in I}$ and $\ell = \ell_k$, it removes the communication and continues with $G_k$. If $G = r \to s : \{\ell_i(S_i).G_i\}_{i \in I}$ with $\{r, s\} \cap \{p, q\} = \emptyset$ and $p, q$ occurring in every $G_i$, it consumes in every branch. Reduction $G \Rightarrow G'$ of global types is the smallest preorder containing $G \Rightarrow G \setminus p \xrightarrow{\ell} q$.

1. **Subject reduction.** If $\vdash M : G$ and $M \to M'$, then $\vdash M' : G'$ for some $G'$ with $G \Rightarrow G'$.
2. **Progress.** If $\vdash M : G$, then either $M \equiv p \triangleleft \mathbf{0}$ or $M \to M'$ for some $M'$.
3. **Type safety.** If $\vdash M : G$, then $M$ is not stuck, and by subject reduction neither is any session it reduces to.

After a step, the projection of the consumed global type can require fewer external choices than before. The reduced process is still typed through subtyping.

## Depends on

- [Global types and projection in multiparty session types](global-types-and-projection-in-multiparty.md)

## Sources

- N. Yoshida and L. Gheri, "A very gentle introduction to multiparty session types", *16th International Conference on Distributed Computing and Internet Technology (ICDCIT 2020)*, LNCS 11969, Springer, 2020, pp. 73–93, <http://mrg.doc.ic.ac.uk/publications/a-very-gentle-introduction-to-multiparty-session-types/main.pdf>: Definition 1 (stuck sessions), Section 4 (the typing system), Definition 7 (consumption and reduction of global types), Example 9, and Theorems 1 (subject reduction), 2 (progress) and 3 (type safety).
- K. Honda, N. Yoshida and M. Carbone, "Multiparty asynchronous session types", *Journal of the ACM* 63(1), Article 9, 2016.
