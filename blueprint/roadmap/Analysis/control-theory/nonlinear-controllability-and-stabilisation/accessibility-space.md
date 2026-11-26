# Accessibility space of a driftless system at a point

For the driftless control-affine system $\dot x = \sum_{i=1}^m u_i f_i(x)$, the accessibility space at $x$ is the span of the values at $x$ of the fields $f_i$ and of all their [iterated Lie brackets](iterated-lie-brackets.md), which are defined for arbitrary fields, with Fréchet derivatives taken to be $0$ where they do not exist. For smooth fields it is $\{ g(x) : g \in \operatorname{Lie}(\{f_1, \dots, f_m\}) \}$ (Coron, *Control and Nonlinearity*, AMS 2007, Definition 3.13 and the formula for $A(x_e, u_e)$ before Definition 3.16, at $u_e = 0$). The **Lie algebra rank condition** at $x$ (Coron, Definition 3.16) says that it is the whole state space. This driftless space does not see a drift: for constant input fields $b_j$ it is just $\operatorname{span}\{b_j\}$. Coron's $A(x_e, u_e)$ for a control-affine system with drift $f_0$ also contains the brackets with $f_0$, and for a linear system $\dot x = Ax + Bu$ it reduces to the Kalman subspace (Coron, (3.33)); that version is not considered here.

## Background

- [Iterated Lie brackets of a family of vector fields](iterated-lie-brackets.md): the fields whose values are taken.
- [Kalman subspace](../controllability-of-linear-systems/kalman-subspace.md): the linear counterpart, $\operatorname{Span} \{ A^i B u \}$.
