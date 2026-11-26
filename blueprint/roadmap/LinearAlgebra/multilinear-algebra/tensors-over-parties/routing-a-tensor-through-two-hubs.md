# Routing a tensor through two hubs

Let $t$ be a tensor over parties $I=I_1\sqcup I_2$ that is a sum of $r$ products of a tensor on $I_1$ and a tensor on $I_2$. Then $t$ is a restriction of the tensor obtained by connecting every party of $I_1$ to a hub party $h_1$ and every party of $I_2$ to a hub $h_2$ by suitable wires and joining $h_1,h_2$ by a wire of dimension $r$; hence for every spectral point $F$, $F(t)$ is bounded by the product of the values of the network's wires and local tensors. More generally the value of a tensor network is a restriction of the product of its edge wires and vertex tensors.

## Proof sketch

Each of the $r$ summands is selected by the index on the hub-to-hub wire; the hubs distribute it to the parties of their side through the local tensors, which realizes $t$ as a contraction, i.e. a restriction of a product of wires and local tensors.

## Depends on

- [Tensors over a finite set of parties and the restriction preorder](tensors-over-a-set-of-parties.md)
- [Upper functionals and spectral points on tensors](upper-functionals-and-spectral-points.md)

## Sources

- Anthropic, "VP ≠ VNP over every field", manuscript, 2026.
