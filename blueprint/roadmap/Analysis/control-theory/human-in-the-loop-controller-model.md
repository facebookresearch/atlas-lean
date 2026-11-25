# Human-in-the-loop controller model

Let $X$ and $Y$ be disjoint finite sets of input and output variables, with input alphabet $\mathcal X = 2^X$ and output alphabet
$\mathcal Y = 2^Y$. A finite-state (Mealy) transducer is a tuple $M = (Q, q_0, \mathcal X, \mathcal Y, \rho, \delta)$ with a finite set
$Q$ of states, an initial state $q_0$, a transition function $\rho : Q \times \mathcal X \to Q$ and an output function
$\delta : Q \times \mathcal X \to \mathcal Y$; on an input word $x_0 x_1 \cdots$ its run is $q_0 q_1 \cdots$ with $q_{k+1} = \rho(q_k, x_k)$,
and it outputs $\delta(q_0, x_0)\, \delta(q_1, x_1) \cdots$. A labelling $F : Q \to \{\mathrm{true}, \mathrm{false}\}$ marks the
failure-prone states.

A human-in-the-loop controller is the composition of an auto-controller $AC$ and an advisory controller $VC$, both finite-state
transducers, with a human operator $HC$ that has the same interface as $AC$: $AC$ and $HC$ read $X \cup \{\mathit{auto}\}$ and write $Y$,
and $VC$ writes the single Boolean variable $\mathit{auto}$, whose value false means that $VC$ asks the human to take over. A Boolean
variable $\mathit{active}$ records whether the human is in control; when it is true the output of $HC$ is the output of the composite
controller, and otherwise the output of $AC$ is. The human need not be a transducer: $HC$ may be an arbitrary relation from inputs to
outputs, restricted only by explicitly stated assumptions. One step is one transition, in which an input is read and an output written.
Specifications are temporal properties of the input and output words (GR(1) formulas in the source's synthesis theorem). No behavioural
model of people beyond the stated assumptions is part of the definition.

## Related topics

- [Interactive device state machines](../../ComputerScience/program-logics-and-verification/interactive-device-state-machines.md)

## Sources

- W. Li, D. Sadigh, S. S. Sastry and S. A. Seshia, *Synthesis for Human-in-the-Loop Control Systems*, TACAS 2014, §3.1 (finite-state transducers and failure-prone states) and §3.2 (agents as automata). <https://sites.bu.edu/depend/files/2017/02/hilp-tacas14.pdf>
