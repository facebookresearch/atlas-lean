# Privacy blanket amplification and single-message summation in the shuffle model

Every $\varepsilon_0$-local randomizer can be written as a mixture $R(x) = (1 - \gamma) R'(x) + \gamma\,\omega$ with a data-independent **privacy blanket** distribution $\omega$ and $\gamma$ determined by $R$ (the total variation mass shared by all output distributions). After shuffling, the about $\gamma n$ blanket samples mask the differing user's report, which gives an amplification bound of the form $\varepsilon = O\big(\sqrt{\log(1/\delta)/(\gamma n)}\big)$ (for $\gamma n \gtrsim \log(1/\delta)$) that extends earlier shuffle amplification to a wider parameter range. As an application, real summation in the single-message shuffle model admits a protocol whose mean squared error grows polynomially in $n$ at a much slower rate than local protocols (whose error has standard deviation $\Theta(\sqrt{n})$), with better accuracy and communication than earlier protocols, and a matching lower bound shows that this polynomial growth is necessary for single-message protocols.

## Proof sketch

Decompose the output law as a common part plus a data-dependent remainder; conditioned on which users drew from the blanket, the shuffled output depends on the differing user only through its non-blanket report, hidden among a binomial number of blanket samples. A Chernoff bound on the number of blanket samples and a likelihood-ratio bound for multinomial counts give the amplification. The summation protocol randomizes discretized values with a blanket that is uniform over the message space; the lower bound analyzes the counts any single-message protocol must reveal.

## Depends on

- [Local randomizers and the shuffle model](shuffle-model.md)
- [Amplification by shuffling from local to central privacy](amplification-by-shuffling-local-to-central.md)

## Proof depends on

- [Local randomizers and the shuffle model](shuffle-model.md)
- [Amplification by shuffling from local to central privacy](amplification-by-shuffling-local-to-central.md)

## Sources

- B. Balle, J. Bell, A. Gascon, K. Nissim, "The Privacy Blanket of the Shuffle Model", CRYPTO (2019), arXiv:1903.02837.
