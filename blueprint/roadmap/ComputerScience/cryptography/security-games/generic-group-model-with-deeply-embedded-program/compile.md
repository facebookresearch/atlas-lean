# Compiling generic-group programs to oracle computations

Let `L` be a type of labels with decidable equality. Given an environment `env
: Fin n → L`, `GProg.compile env` translates a generic-group program into an
oracle computation: `ret i` returns `env i`; `mul` and `inv` issue one oracle
query on the indexed labels and compile the continuation in the environment
extended by the answer; `eqTest i j` branches on whether `env i = env j`.
Compiled programs hold no label values beyond their inputs.
