# Long short-term memory (LSTM) cell

An LSTM without peephole connections carries both a cell state $c_t$ and a visible state $h_t$, each in $\mathbb R^m$. Put $u=[x_t;h_{t-1}]$. For each gate $a\in\{i,f,o\}$ set $a_t=\operatorname{sigmoid}(W_a u+b_a)$; let $g_t=\tanh(W_g u+b_g)$. Given $c_0,h_0$, one step is

$$c_t=f_t\odot c_{t-1}+i_t\odot g_t,\qquad h_t=o_t\odot\tanh(c_t).$$

Products and activations are coordinatewise. The forget gate scales the old cell, the input gate scales its proposed addition, and the output gate controls how much of the cell is visible. The matrices are shared across time, not across gates.

## Depends on

- [Recurrent neural network (RNN)](recurrent-neural-network.md)
- [Coordinatewise activation](coordinatewise-activation.md)

## Sources

- Zaremba, Sutskever and Vinyals, [*Recurrent Neural Network Regularization*](https://arxiv.org/abs/1409.2329) (ICLR 2015), the LSTM equations immediately before figure 1: the input, forget and output gates use sigmoid; the candidate and cell readout use tanh.
