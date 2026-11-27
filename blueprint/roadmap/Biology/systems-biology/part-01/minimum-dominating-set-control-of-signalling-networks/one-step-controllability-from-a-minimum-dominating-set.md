# One-step controllability of a nonlinear network from a minimum dominating set

Let $G = (V, E)$ be a directed network on nodes $x_1, \dots, x_n$ (for example proteins of a signalling network). A set $U \subseteq V$ is a **dominating set** if every node not in $U$ has an in-neighbour in $U$; a **minimum dominating set** (MDS) is one of least size. Consider discrete-time dynamics

$$x_i(t+1) = f_i\big(x_{i_1}(t), \dots, x_{i_k}(t)\big),$$

where $x_{i_1}, \dots, x_{i_k}$ are the in-neighbours of $x_i$, and fix a target domain $D \subseteq \mathbb{R}$. Assume:

- **Condition (#2):** each $f_i$ can be steered by any single argument: for every $j$, every choice of the other $k - 1$ arguments in $\mathbb{R}$ and every $b \in D$, there is $a_j \in \mathbb{R}$ with $f_i(a_1, \dots, a_k) = b$;
- **Condition (#1):** every node of an MDS $U$ receives its own control signal $u_i(t)$, which overrides its state, and every edge $(x_j, x_i)$ leaving $U$ carries its own control signal $u_{j,i}(t)$, which replaces the value $x_j(t)$ seen by $x_i$.

Write the controlled system as $x(t+1) = F(x(t), u(t))$.

**Proposition (Methods, Proposition 1 of the source).** Under Conditions (#1) and (#2), for every $a \in \mathbb{R}^n$ and every $b \in D^n$ there is a control vector $u$ with $b = F(a, u)$: the network can be driven from any state to any state in $D^n$ in one step.

## Expansion

For $x_i \in U$ set $u_i = b_i$. For $x_i \notin U$, domination gives at least one in-neighbour $x_{i_1} \in U$; set the signals on the other edges from $U$ into $x_i$ to $0$, keep the remaining inputs at their current values, and choose $u_{i_1, i}$ by Condition (#2) so that $f_i = b_i$. Condition (#2) holds with $D = \mathbb{R}$ for every linear $f_i$ depending on all its inputs, for products $\alpha_i x_{i_1} \cdots x_{i_k}$ on nonzero values, and for logistic functions with values in $(0, 1)$. For linear dynamics, the source cites that Condition (#1) with the MDS as driver set gives structural controllability (Nacher and Akutsu 2012). In contrast with maximum-matching driver sets, whose critical nodes are exactly the nodes of in-degree zero, the MDS model in the source identifies far fewer driver nodes in human signalling networks infected by HIV-1 or HCV, and viral proteins preferentially target MDS-critical nodes. The roles of nodes across all MDSs are related in indispensable nodes are MDS-critical.

## Sources

- V. Ravindran, J. C. Nacher, T. Akutsu, M. Ishitsuka, A. Osadcenco, V. Sunitha, G. Bagler, J.-M. Schwartz and D. L. Robertson, *Network controllability analysis of intracellular signalling reveals viruses are actively controlling molecular systems*, Scientific Reports 9 (2019), 2066. DOI: <https://doi.org/10.1038/s41598-018-38224-9>. PMCID: PMC6375943.
- J. C. Nacher and T. Akutsu, *Dominating scale-free networks with variable scaling exponent: heterogeneous networks are not difficult to control*, New Journal of Physics 14 (2012), 073005.
