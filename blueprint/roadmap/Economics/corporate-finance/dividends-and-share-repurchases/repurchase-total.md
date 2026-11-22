# Shareholder wealth after a share repurchase

For real `N` (shares), `P` (share price) and `C` (cash paid out), total shareholder wealth under a
share repurchase is `C + (N - C / P) * P`: the cash `C` paid to selling shareholders plus the
market value of the `N - C / P` remaining shares, with the repurchase taken to execute at the
pre-payout price `P`. This price convention encodes the frictionless assumption (no taxes, fees,
price impact, or signalling), and with it the total is `N * P` whenever `P ≠ 0`; for `P = 0` the
formula gives `C`, by the convention x / 0 = 0.
