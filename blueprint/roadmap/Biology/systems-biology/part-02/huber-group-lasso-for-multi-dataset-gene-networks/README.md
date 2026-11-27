# Huber group lasso for multi-dataset gene networks

Inference of one gene regulatory network topology from several time-course expression datasets. Each dataset follows a discretized linear ODE model with its own regulatory strengths but a shared zero pattern. A group lasso over the per-dataset copies of each edge enforces the shared topology, and the Huber loss makes the fit robust to outliers. A majorize-then-block-descent algorithm solves the convex problem, and stability selection turns it into edge scores.

- [Huber group lasso for shared-topology gene regulatory networks](huber-group-lasso-for-shared-topology-gene-regulatory-networks.md)
- [Majorized block descent for the Huber group lasso](majorized-block-descent-for-the-huber-group-lasso.md)
