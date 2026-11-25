# Data refinement by forward simulation

An *abstract data type* over operation names $O$ is a state set with a set of initial states and, for each operation $o \in O$, argument
$a$ and result $r$, a step relation $s \xrightarrow{o(a)/r} s'$. A finite *operation trace* of a data type is a sequence $o_1(a_1)/r_1, \dots, o_k(a_k)/r_k$
for which there are an initial state $s_0$ and steps $s_{i-1} \xrightarrow{o_i(a_i)/r_i} s_i$ for $i = 1, \dots, k$.

Let $A$ and $C$ be data types over the same operation names. Suppose $J$ is a predicate on concrete states and $\alpha$ maps concrete
states satisfying $J$ to abstract states, such that

1. every concrete initial state $c_0$ satisfies $J$ and $\alpha(c_0)$ is an abstract initial state, and
2. for every concrete state $c$ with $J(c)$ and every concrete step $c \xrightarrow{o(a)/r} c'$, $J(c')$ holds and $\alpha(c) \xrightarrow{o(a)/r} \alpha(c')$ is an
   abstract step.

Then every finite operation trace of $C$ is an operation trace of $A$, and more generally $\alpha$ maps every finite or infinite sequence
of concrete steps from an initial state to a sequence of abstract steps with the same labels. Hence a client that interacts with
the data type only through operations, arguments and results observes no finite behavior with $C$ that it could not observe with $A$.
The argument is induction along the steps. It concerns safety behaviors only; termination and divergence of operations are not
compared.

## Sources

- M. Abadi and L. Lamport, "The existence of refinement mappings", *Theoretical Computer Science* 82(2):253–284, 1991, <https://lamport.azurewebsites.net/pubs/abadi-existence.pdf>: Section 1.2 (implementation as inclusion of externally visible behaviors and refinement mappings preserving state-machine behavior), conditions R1–R3 and Proposition 1. This page is the special case without internal or stuttering steps, with the operation labels as the externally visible part.
