# Information Theory

Information theory quantifies information, uncertainty, compression, and transmission through entropy and coding.

The two largest fields, with nearly two thirds of the articles between them, are
[source coding](source-coding/README.md) and [error-correcting codes](error-correcting-codes/README.md). Source coding
is mostly [Huffman coding](source-coding/huffman-coding/README.md) and its optimality, with
[Shannon's source coding theorem](source-coding/shannon-s-source-coding-theorem/README.md), which puts the least
expected length of a uniquely decodable code over $q \ge 2$ letters between the base-$q$ entropy and one letter more.
Error-correcting codes run from [linear codes](error-correcting-codes/linear-codes/README.md) and the perfect Hamming
$(7,4)$ code to [Reed–Solomon codes](error-correcting-codes/reed-solomon-codes/README.md), which meet the Singleton
bound, and good locally testable codes. [Entropy and mutual information](entropy-and-mutual-information/README.md) and
[information inequalities](information-inequalities/README.md) such as Fano's set up the basic quantities, and
[channel simulation](channel-simulation/README.md) asks how small $H(Y \mid S)$ can be for an auxiliary variable $S$,
independent of the input $X$, that determines the output $Y$ together with $X$.

- [Entropy and mutual information](entropy-and-mutual-information/README.md)
- [Information inequalities](information-inequalities/README.md)
- [Source coding](source-coding/README.md)
- [Channel simulation](channel-simulation/README.md)
- [Error-correcting codes](error-correcting-codes/README.md)
