# Secure two-party inference with a public architecture

A *secure inference protocol* for a fixed public architecture lets a server holding the network's parameters $M$ and a client holding an input $x$ give the client $M(x)$, so that a semi-honest client's view is simulatable from $(x,M(x))$ and a semi-honest server's view from $M$ alone.

Fix a public *architecture* $\mathcal{A}$: the number of layers, the type of each layer (linear or activation, and which activation), and the input and output dimension of each layer. The *parameters* $M=(M_1,\dots,M_\ell)$ are the weights and biases of the linear layers, and $M(x)$ is the output of $\mathcal{A}$ with parameters $M$ on input $x$. A two-party protocol $\Pi$ between a server with input $M$ and a client with input $x$, both knowing $\mathcal{A}$, is a *secure inference protocol for $\mathcal{A}$* if:

- *Correctness.* For every $M$ and every $x$, the client's output at the end of $\Pi$ is $M(x)$.
- *Security against a semi-honest client.* There is an efficient simulator $\mathrm{Sim}_C$ with $\mathrm{View}_C^{\Pi}\approx_c\mathrm{Sim}_C(x,M(x))$, the view consisting of the client's input, randomness and transcript.
- *Security against a semi-honest server.* There is an efficient simulator $\mathrm{Sim}_S$ with $\mathrm{View}_S^{\Pi}\approx_c\mathrm{Sim}_S(M)$.

The leakage is exactly $\mathcal{A}$ to both parties, plus $M(x)$ to the client. Other systems fix other profiles, which are different functionalities: Gazelle's protocol also hides filter and stride sizes and which linear layers are convolutional, and reveals only the number of layers and the size of each. When the architecture is chosen by a search that looks at training data, revealing it reveals that search's choices; Delphi's planner makes $\ell$ binary choices and so reveals at most $\ell$ bits.

## Depends on

- [Two-party security against semi-honest adversaries](../../signatures-and-protocols/secure-multiparty-computation/two-party-security-against-semi-honest.md)

## Proof depends on

None.

## Expansion

A definition; it instantiates the existing semi-honest two-party notion with the functionality $(M,x)\mapsto(\bot,M(x))$ and the public data $\mathcal{A}$.

## Sources

- Pratyush Mishra, Ryan Lehmkuhl, Akshayaram Srinivasan, Wenting Zheng, Raluca Ada Popa, "Delphi: A Cryptographic Inference Service for Neural Networks", 29th USENIX Security Symposium (2020), §§2.2–2.3 and Definition 4.1, [USENIX open-access copy](https://www.usenix.org/conference/usenixsecurity20/presentation/mishra).
- Chiraag Juvekar, Vinod Vaikuntanathan, Anantha Chandrakasan, "GAZELLE: A Low Latency Framework for Secure Neural Network Inference", 27th USENIX Security Symposium (2018), [USENIX copy](https://www.usenix.org/conference/usenixsecurity18/presentation/juvekar); preprint arXiv:1801.05507v1. Section 2.3.
