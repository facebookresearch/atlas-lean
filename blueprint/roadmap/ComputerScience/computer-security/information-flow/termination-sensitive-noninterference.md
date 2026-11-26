# Termination-sensitive noninterference

Consider a deterministic imperative language over high and low variables, whose semantics maps an input state $s$ either to an output state or to $\bot$ when the
program does not terminate. States are low-equivalent, $s =_L s'$, if they agree on the low variables. A program $C$ satisfies *termination-sensitive
noninterference* if for all $s_1 =_L s_2$, either $C$ diverges from both, or it terminates from both in low-equivalent final states.

Volpano and Smith obtain this property with a security type system that, beyond the usual rules preventing explicit and implicit flows to low
variables, disallows loops with high guards and requires that conditionals with high guards contain no loops in their branches. Well-typed programs then
satisfy termination-sensitive noninterference; in particular whether a well-typed program terminates does not depend on its high inputs. Without the
loop restrictions, $\mathbf{while}\ h = 1\ \mathbf{do}\ \mathbf{skip}$ leaks $h$ through termination.

## Depends on

- [Security levels, policies and low equivalence](security-levels-policies-and-low-equivalence.md)

## Sources

- A. Sabelfeld and A. C. Myers, "Language-based information-flow security", *IEEE Journal on Selected Areas in Communications* 21(1):5–19, 2003, <https://www.cs.cornell.edu/andru/papers/jsac/sm-jsac03.pdf>: Section II (the semantic noninterference condition with low-view relations) and Section IV, "Termination channels" (the termination-sensitive low view and the loop restrictions of the Volpano–Smith type system).
