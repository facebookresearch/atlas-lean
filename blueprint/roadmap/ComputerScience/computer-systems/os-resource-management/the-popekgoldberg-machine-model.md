# The Popek–Goldberg machine model

Popek and Goldberg state their virtualization theorem for a model of *third-generation machines*. A machine state consists of four parts:
- executable storage;
- a processor mode, *supervisor* or *user*;
- a program counter;
- a relocation-bounds register that confines user-mode memory accesses.

Instructions may *trap*, transferring control to the supervisor. Two classes of instructions matter:
- an instruction is *privileged* if it traps in user mode and does not trap in supervisor mode;
- an instruction is *sensitive* if it is *control-sensitive*, attempting to change the configuration of system resources such as the mode or the relocation register, or *behaviour-sensitive*, behaving differently depending on that configuration.

A *virtual machine monitor* must have three properties:
- **equivalence:** programs run under it as on the original machine, apart from timing and resource availability;
- **efficiency:** a dominant subset of instructions executes directly on the hardware;
- **resource control:** the monitor is in complete control of system resources.

## Expansion

This page becomes ready once:

- the four-part machine state, the trap mechanism, the classes of privileged, control-sensitive and behaviour-sensitive instructions, and the exact statements of the three monitor properties are checked against the primary paper, which has not been opened; the secondary summary covers only the three properties, in looser wording (efficiency as only minor decreases in speed), and the privileged and sensitive classes (statement prerequisite; source not yet opened).

## Sources

- M. Kasick, G. Willen and M. Cui, *Virtualization*, lecture slides, 15-410 Operating System Design and Implementation, Carnegie Mellon University, 16 April 2007, <https://www.cs.cmu.edu/~410-s07/lectures/L38_Virtualization.pdf>: the three monitor properties (equivalence, efficiency, resource control), the classification of privileged instructions (trap in user mode, not in supervisor mode) and sensitive instructions (change, or behave differently depending on, the system configuration), and the x86 instructions that are sensitive but unprivileged. This is a secondary source.
