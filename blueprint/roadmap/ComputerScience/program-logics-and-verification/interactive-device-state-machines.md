# Interactive device state machines

An interactive system model is a finite labelled transition system with states $Q$, an initial state $q_0$, a finite set $\Sigma$ of user
actions and a transition relation $\to\ \subseteq Q \times \Sigma \times Q$ (deterministic when it is the graph of a partial function
$Q \times \Sigma \to Q$), together with an observation map $\mathrm{obs} : Q \to \mathrm{Disp}$ giving what is displayed in each state, and
optionally a mode map $\mathrm{mode} : Q \to M$. It is a labelled transition system with an observation map added. It makes no claim about
human cognition.

## Expansion

This node states a precise definition.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Labelled transition system.

## Sources

- H. Thimbleby, *User Interface Design With Matrix Algebra*, ACM Trans. Comput.-Hum. Interact. 11(2) (2004), 181–236, §2.3 (interactive devices as finite state machines whose transitions are labelled by user actions; nondeterministic machines in the Appendix). <https://citeseerx.ist.psu.edu/document?doi=f5f87ecf5b9482b065e01f3eb0758ed7dfdd7882&repid=rep1&type=pdf>
- M. Heymann and A. Degani, *Constructing Human-Automation Interfaces: A Formal Approach*, HCI-Aero 2002, the transmission example (a machine model whose states are grouped into modes, and the display shown to the user). <https://cdn.aaai.org/HCI/2002/HCI02-019.pdf>
- Formal methods in HCI (chapter) — Alan Dix (hcibook.com author page). <https://www.hcibook.com/alan/papers/formal-chapter-95/> Background reference.
