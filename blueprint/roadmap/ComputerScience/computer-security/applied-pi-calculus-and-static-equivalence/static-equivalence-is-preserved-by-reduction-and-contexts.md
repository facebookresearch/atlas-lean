# Static equivalence is invariant under reduction and closing contexts

**Lemma.** Let $A$ and $B$ be closed extended processes of the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md). If $A \equiv B$ or $A \to B$, then $A \approx_s B$. If $A \approx_s B$,
then $E[A] \approx_s E[B]$ for every closing evaluation context $E$. Here $\equiv$ is [structural equivalence](structural-equivalence-in-the-applied-pi-calculus.md),
$\to$ [internal reduction](internal-reduction-in-the-applied-pi-calculus.md), and $\approx_s$ [static equivalence](frames-and-static-equivalence.md) of the frames
of the processes.

## Depends on

- [Internal reduction in the applied pi calculus](internal-reduction-in-the-applied-pi-calculus.md)
- [Frames and static equivalence](frames-and-static-equivalence.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)
- [Structural equivalence in the applied pi calculus](structural-equivalence-in-the-applied-pi-calculus.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 4.2, Lemma 4.1 (proved in Appendix A).
