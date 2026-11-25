# The Popek–Goldberg virtualization theorem

For a conventional third-generation machine in the [Popek–Goldberg model](the-popekgoldberg-machine-model.md), a virtual machine monitor with the properties of equivalence, efficiency and resource control may be constructed if the set of sensitive instructions is a subset of the set of privileged instructions. In other words, every sensitive instruction must trap when executed in user mode.

The paper also gives variants for *recursive* virtualization, a monitor that can run a copy of itself, and for *hybrid* monitors, which interpret all instructions executed in virtual supervisor mode.

The classical x86 architecture violates the condition: seventeen or more instructions, among them $\mathtt{SGDT}$, $\mathtt{SIDT}$, $\mathtt{SMSW}$, $\mathtt{PUSHF}$ and $\mathtt{POPF}$, are sensitive but unprivileged.

## Depends on

- [The Popek–Goldberg machine model](the-popekgoldberg-machine-model.md)

## Expansion

This page becomes ready once:

- the main theorem is stated and checked against the primary paper (statement prerequisite; source not yet opened);
- the recursive-virtualization and hybrid-monitor variants are stated and checked against the primary paper (statement prerequisite; source not yet opened).

## Sources

- M. Kasick, G. Willen and M. Cui, *Virtualization*, lecture slides, 15-410 Operating System Design and Implementation, Carnegie Mellon University, 16 April 2007, <https://www.cs.cmu.edu/~410-s07/lectures/L38_Virtualization.pdf>: the quoted theorem ("a virtual machine monitor may be constructed if the set of sensitive instructions for that computer is a subset of the set of privileged instructions"), the list of sensitive but unprivileged x86 instructions, and examples of architectures that meet the requirement. This is a secondary source.
