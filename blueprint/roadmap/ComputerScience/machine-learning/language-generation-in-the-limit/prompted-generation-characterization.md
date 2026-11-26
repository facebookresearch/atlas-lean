# Prompted generation is characterized by the prompted closure dimension

In **prompted generation**, at each step the generator additionally receives a prompt (an arbitrary string from a prompt space, chosen adversarially) and must output a new string of the target language that is valid for the prompt (for example, extends it). Extending the closure operator to prompted closures defines the **prompted closure dimension**; then a class is prompted uniformly generatable if and only if its prompted closure dimension is finite, and it is prompted non-uniformly generatable if and only if it is a countable increasing union of classes of finite prompted closure dimension. These characterizations generalize the corresponding results without prompts and part of the prompted-generation results of Kleinberg and Mullainathan.

## Proof sketch

The proofs follow the unprompted case: for each prompt, the prompted closure of the seen strings is the set of strings valid for the prompt in every consistent language; finiteness of the dimension guarantees that after a bounded number of distinct examples this set is infinite (or the sample is unrealizable), so the generator can output an unseen element, and infinite dimension lets the adversary choose a prompt whose closure it exhausts.

## Depends on

- [Closure dimension and uniform and non-uniform generatability](closure-dimension.md)

## Proof depends on

- [The closure dimension characterizes uniform generatability](closure-dimension-characterizes-uniform-generation.md)

## Sources

- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714.
- J. Kleinberg, S. Mullainathan, "Language Generation in the Limit", NeurIPS (2024), arXiv:2404.06757.
