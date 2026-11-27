# Attacker knowledge for programs with low events

Consider the while language with expressions $e ::= n \mid x \mid e \mathbin{op} e$ and commands
$c ::= \mathbf{skip} \mid x := e \mid c; c \mid \mathbf{if}\ e\ \mathbf{then}\ c\ \mathbf{else}\ c \mid \mathbf{while}\ e\ \mathbf{do}\ c \mid x := \mathrm{declassify}(e)$, whose variables
have levels $L$ or $H$ recorded in an environment $\Gamma$. Its small-step semantics on configurations $\langle M, c \rangle$ produces *low events*: an assignment to a low
variable produces an event recording the low part of the memory, and termination produces the low event $\downarrow$, after which no event follows. We write
$\langle M, c\rangle \xrightarrow{\vec\ell}{}^{*} \langle M', c'\rangle$ (or $\to^* M'$ on termination) for a run producing the sequence $\vec\ell$, and $M_L$ for the low projection of a
memory $M$.

For a command $c$ and a low projection $M^0_L$, let $L(c, M^0_L)$ be the set of low event sequences produced by terminating runs from memories $M$ with $M_L = M^0_L$,
and $\hat L(c, M^0_L)$ its prefix closure. For $\vec\ell \in \hat L(c, M^0_L)$ the attacker's *knowledge* is the set of possible initial memories

$$k(c, M^0_L, \vec\ell) = \{ M \mid M_L = M^0_L \wedge \exists M', c'.\ \langle M, c\rangle \xrightarrow{\vec\ell}{}^{*} \langle M', c'\rangle \vee \langle M, c\rangle \xrightarrow{\vec\ell}{}^{*} M' \},$$

the *initial knowledge* is $k(c, M^0_L) = \{ M \mid M_L = M^0_L \wedge \exists M', \vec\ell.\ \langle M, c\rangle \xrightarrow{\vec\ell}{}^{*} M'\}$, and the termination-insensitive knowledge is
$k_\downarrow(c, M^0_L, \vec\ell) = k(c, M^0_L, \vec\ell) \cap k(c, M^0_L)$, with $k_\downarrow(c, M^0_L, \vec\ell_0) = k(c, M^0_L)$ for the empty sequence. A smaller set means that the
attacker knows more.

## Depends on

- [Security levels, policies and low equivalence](../information-flow/security-levels-policies-and-low-equivalence.md)

## Sources

- A. Askarov and A. Sabelfeld, "Gradual release: unifying declassification, encryption and key release policies", *Proceedings of the 2007 IEEE Symposium on Security and Privacy*, copy at <https://www.cs.cornell.edu/~aslan/askarov-sabelfeld-sp07.pdf>: Section 2, Figure 1 (the language) and the definitions of low events, release events, $L(c, M^0_L)$ and the knowledge sets $k$, $k(c, M^0_L)$ and $k_\downarrow$.
