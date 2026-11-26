# Expected precision at a cutoff

For a weight $\mu$ on relevance vectors $\mathrm{rel} \in \{0, 1\}^N$ and a ranked prefix $r_1, \dots, r_k$ of documents, the expected precision at $k$ is

$$\sum_{\mathrm{rel}} \mu(\mathrm{rel}) \cdot \mathrm{P@}k(\mathrm{rel}, r),$$

where $\mathrm{P@}k$ is the fraction of $r_1, \dots, r_k$ that are relevant (and $0$ when $k = 0$). When $\mu$ is a probability mass function this is the expectation of precision at $k$.
