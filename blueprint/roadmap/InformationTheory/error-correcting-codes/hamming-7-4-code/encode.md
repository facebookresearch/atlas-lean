# Encoder of the Hamming code

Let $G$ be the $4 \times 7$ generator matrix over
$\mathbb{F}_2$ with rows $(1,1,1,0,0,0,0)$, $(1,0,0,1,1,0,0)$, $(0,1,0,1,0,1,0)$ and
$(1,1,0,1,0,0,1)$. A message $m \in \mathbb{F}_2^4$ is encoded as the word
$mG \in \mathbb{F}_2^7$, the combination of the rows of $G$ with coefficients $m$.
