# LTL model checking is language inclusion

All initial infinite runs of a transition system satisfy an LTL formula $\varphi$ iff
$L_\omega(A_P) \subseteq L_\omega(A_\varphi)$, where $A_P$ is the Büchi automaton of the system
and $A_\varphi$ the Büchi automaton of $\varphi$.

This is the automata-theoretic statement of the verification problem: programs and
specifications both describe sets of infinite computations, and correctness is inclusion.

## Informally uses

- [The language of the system automaton is the set of runs](mem-system-automaton-iff.md).
- [Büchi automaton accepts exactly the satisfying words](mem-buchi-iff.md).

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 4.2.
- M. Y. Vardi and P. Wolper, "An automata-theoretic approach to automatic program
  verification", in *Proc. 1st IEEE Symposium on Logic in Computer Science* (LICS 1986),
  332-344.
