# Residual networks as discretised flows

A residual network with the $1/L$ scaling, $z_{l+1} = z_l + \frac1L g_l(z_l)$ for
$l = 0, \dots, L - 1$, is the explicit Euler scheme with step $1/L$ for an ordinary differential
equation $\dot z = g(t, z)$ on $[0, 1]$: deep networks are discretised dynamical systems, and their
continuous-depth limit is a flow. This is the dynamical-systems view of deep learning of W. E
and of E, Han and Li, in which training becomes an optimal control problem over the flow. For a
time-dependent block $g$ that is $C^2$ and globally Lipschitz in the state (for instance
$U(t) \sigma(W(t) z)$ with smooth weights and a $C^2$ activation with bounded derivative, such as
$\tanh$), the output of the depth-$L$ network is within $C/L$ of the
time-$1$ value of the flow, uniformly in the depth, by the first-order convergence of Euler's
method.

- [Residual networks converge to their continuous-depth flow at rate $1/L$](residual-network-flow-error-le.md)

## Related topics

- [Euler method](../../../../Analysis/numerical-analysis/euler-method/README.md): the first-order convergence of the explicit Euler scheme, of which the depth-uniform bound for residual networks is the case $h = 1/L$.
- [Two-layer neural networks and Barron space](../two-layer-neural-networks-and-barron-space/README.md): the shallow counterpart; E, Ma and Wu attach flow-induced function spaces to residual networks as they attach the Barron space to two-layer networks.
- [Backpropagation](../backpropagation/README.md): the gradient of a residual network, the discrete adjoint of the flow.
