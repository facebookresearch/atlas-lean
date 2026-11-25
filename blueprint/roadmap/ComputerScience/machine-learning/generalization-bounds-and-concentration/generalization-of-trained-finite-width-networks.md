# Generalization of trained finite-width neural networks with feature learning

This node records a research direction: prove nonvacuous generalization guarantees for neural networks of finite width trained by a gradient method, in a regime where the learned features change during training.

## What would settle it

Fix the architecture, initialization, optimizer, step sizes, data distribution family and finite training and sample budgets. Then prove a nonvacuous bound on the population risk of the network actually produced by the training trajectory, in a regime that allows feature learning. Universal approximation, or the existence of a good weight vector, does not show that training reaches it.

## Status

No cited source poses this question in the form above; it is a research direction motivated by the cited results. This page does not certify the status or novelty of any particular formulation.

Suh and Cheng review excess-risk results for neural networks and note that results built on explicit network constructions apply only to the global minimizer of a highly nonconvex landscape, which motivates their review of training dynamics.

This page records a research direction and asserts no theorem or present-status certification.

## Sources

- N. Suh and G. Cheng, "A survey on statistical theory of deep learning: approximation, training dynamics, and generative models", preprint version 3, abstract. <https://arxiv.org/abs/2401.07187>
