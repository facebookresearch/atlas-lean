# Gated recurrent unit (GRU)

For input $x$ and previous state $h$, the original GRU uses reset and update gates $r=\operatorname{sigmoid}(W_rx+U_rh)$ and $z=\operatorname{sigmoid}(W_zx+U_zh)$. Its candidate and next state are

$$\widetilde h=\tanh(Wx+U(r\odot h)),\qquad h'=z\odot h+(1-z)\odot\widetilde h.$$

All gates have the state dimension. In this bias-free convention, $z$ weights the **old** state and the reset gate acts **before** $U$. Moving it outside that matrix product generally changes the cell. Unlike the LSTM, the GRU has no separate cell state.

## Depends on

- [Recurrent neural network (RNN)](recurrent-neural-network.md)
- [Coordinatewise activation](coordinatewise-activation.md)

## Sources

- Cho et al., [*Learning Phrase Representations using RNN Encoder–Decoder for Statistical Machine Translation*](https://aclanthology.org/D14-1179/) (EMNLP 2014), §2.3, equations (5)–(8); the experiments use tanh for the candidate activation in equation (8).
