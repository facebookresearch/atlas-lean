# Neural-network control systems

A neural-network control system iterates a feedback loop in discrete time: a ReLU neural network computes a control input from the current state, and a plant maps the state and the control input to the next state. Its reachability problem asks whether some initial state in a polyhedron reaches a target polyhedron.

**Deep neural networks.** A *neuron* is a map $\nu : \mathbb{R}^m \to \mathbb{R}$, $\nu(\vec{x}) = \sigma\bigl(\sum_{i=1}^m c_i x_i + b\bigr)$ with rational weights $c_i$, rational bias $b$ and activation $\sigma$ either the identity or $\mathrm{ReLU}(y) = \max\{y, 0\}$. A *layer* is a finite sequence of neurons with a common input dimension, and a *deep neural network* (DNN) $N$ is a finite sequence of $k$ layers whose dimensions compose; it computes the composition of its layers, that is, the forward pass through the first $k$ layers of any [feedforward network](../supervised-learning/backpropagation/net.md) whose first $k$ layers are the given ones. All layers except the last are *hidden*.

**Definition (Schilling and Zimmermann).** A *neural-network control system* (NNCS) is a pair $(f, N)$ of a plant $f : \mathbb{R}^{n + p} \to \mathbb{R}^n$ and a DNN $N : \mathbb{R}^n \to \mathbb{R}^p$. From a state $\vec{x}_0 \in \mathbb{R}^n$ it produces $\vec{u}_k = N(\vec{x}_{k-1})$ and $\vec{x}_k = f(\vec{x}_{k-1}, \vec{u}_k)$ for $k \ge 1$; write $\Phi(\vec{x}) = f(\vec{x}, N(\vec{x}))$ for one iteration. A polyhedron is a finite intersection of half-spaces $\{\vec{x} : \langle a, \vec{x} \rangle \le b\}$ with $a \in \mathbb{Q}^n$, $b \in \mathbb{Q}$. The *reachability problem for NNCS* asks, given $N$, $f$, a polyhedron $X_0$ of initial states and a polyhedron $T$ of target states, whether there are $\vec{x}_0 \in X_0$ and $k \in \mathbb{N}$ with $\Phi^k(\vec{x}_0) \in T$. Here $k = 0$ is allowed, so an instance with $X_0 \cap T \ne \emptyset$ is a yes-instance. The source's problem allows any plant; as an input to an algorithm the plant must be given finitely, and the undecidability results use the plant $f(\vec{x}, \vec{u}) = \vec{u}$. The network is given by its rational weights and biases and its activations, and each polyhedron by finitely many rational constraints.

## Depends on

- [Feedforward network](../supervised-learning/backpropagation/net.md)

## Proof depends on

None.

## Expansion

Time is discrete and only the plant's output after each iteration matters; the plant is left abstract as a function, and the undecidability result already holds when the plant simply returns the control input, $f(\vec{x}, \vec{u}) = \vec{u}$.

## Sources

- Christian Schilling and Martin Zimmermann, "The Reachability Problem for Neural-Network Control Systems", Bridging the Gap Between AI and Reality (AISoLA 2023), Lecture Notes in Computer Science, pp. 455–469, Springer, 2024, <https://doi.org/10.1007/978-3-031-73741-1_27>; Definitions 1 and 2 and Problem 1 in Section 2 of arXiv:2407.04988v2 (the copy read), <https://arxiv.org/abs/2407.04988v2>.
